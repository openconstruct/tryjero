/**
 * Trystero WebTorrent - P2P WebRTC networking library
 * A modern JavaScript refactoring of the original Trystero Torrent library by Jerry
 */

// Constants
const LIBRARY_NAME = 'Tryjero';
const SELF_ID = generateRandomId(20);
const DEFAULT_RELAY_REDUNDANCY = 3;
const DEFAULT_TRACKER_URLS = [
  'wss://tracker.webtorrent.dev',
  'wss://tracker.openwebtorrent.com',
  'wss://tracker.btorrent.xyz',
  'wss://tracker.files.fm:7073/announce'
];

// Crypto constants
const CRYPTO_ALGORITHM = 'AES-GCM';
const IS_BROWSER = typeof window !== 'undefined';

// Cached hash values
const hashCache = {};

// WebSocket reconnection timing
const reconnectTimes = {};

// Tracker state storage
const trackerSockets = {};
const trackerHandlers = {};
const trackerIntervals = {};
const trackerAnnouncers = {};
const trackerDefaultInterval = 33333; // ~33 seconds
const pendingOffers = {};
const roomTrackerIntervals = {};

// ICE servers for WebRTC
const defaultIceServers = [
  ...Array(3).fill().map((_, i) => ({ urls: `stun:stun${i || ''}.l.google.com:19302` })),
  { urls: 'stun:global.stun.twilio.com:3478' }
];

// Data transmission constants
const MAX_CHUNK_SIZE = 16369;
const PROGRESS_MAX = 255;
const BUFFER_LOW_EVENT = 'bufferedamountlow';

// Character set for random IDs
const CHARSET = '0123456789AaBbCcDdEeFfGgHhIiJjKkLlMmNnOoPpQqRrSsTtUuVvWwXxYyZz';

/**
 * Generate a random ID of specified length
 * @param {number} length - Length of ID to generate
 * @returns {string} Random ID
 */
function generateRandomId(length) {
  return Array(length).fill()
    .map(() => CHARSET[Math.floor(Math.random() * 62)])
    .join('');
}

/**
 * Create Trystero error with proper formatting
 * @param {string} message - Error message
 * @returns {Error} Formatted error
 */
function createError(message) {
  return Error(`${LIBRARY_NAME}: ${message}`);
}

/**
 * Join a room for P2P communication
 * @param {Object} config - Configuration options
 * @param {string} roomId - Unique room identifier
 * @param {Function} onSignal - Optional signal handler
 * @returns {Object} Room interface
 */
function joinRoom(config, roomId, onSignal) {
  const { appId } = config;
  
  // Validate inputs
  if (!config) {
    throw createError('requires a config map as the first argument');
  }
  
  if (!appId && !config.firebaseApp) {
    throw createError('config map is missing appId field');
  }
  
  if (!roomId) {
    throw createError('roomId argument required');
  }

  // Initialize room storage if not already present
  const roomRegistry = {};
  if (!roomRegistry[appId]) {
    roomRegistry[appId] = {};
  }
  
  if (roomRegistry[appId][roomId]) {
    return roomRegistry[appId][roomId];
  }

  // Core room namespace and keys
  const namespace = joinPaths(LIBRARY_NAME, appId, roomId);
  const namespaceHash = getHash(namespace);
  const selfHash = getHash(joinPaths(namespace, SELF_ID));
  
  // Encryption key derived from password, app, and room
  const encryptionKey = deriveEncryptionKey(config.password || '', appId, roomId);
  
  // Setup encryption functions
  const encryptSignal = async (signal) => ({
    type: signal.type,
    sdp: await encryptSdp(encryptionKey, signal.sdp)
  });
  
  const decryptSignal = async (signal) => ({
    type: signal.type,
    sdp: await decryptSdp(encryptionKey, signal.sdp)
  });

  // Connection management
  let peerConnections = [];
  const trackers = initializeTrackers(config);
  const trackerUpdateIntervals = trackers.map(() => 5333);
  const trackerTimeouts = [];
  
  // Create initial peer connections
  const pendingPeers = Array(20).fill().map(() => createPeerConnection(true, config));
  
  // Peer and connection registries
  const peers = {};
  const pendingConnections = {};

  // Setup trackers and begin connecting
  const trackerSubscriptions = trackers.map(async (tracker, index) => {
    return subscribeToTracker(
      await tracker,
      await namespaceHash,
      await selfHash,
      createSignalHandler(index),
      createOfferBatch
    );
  });

  // Start announcing to trackers
  Promise.all([namespaceHash, selfHash]).then(([roomHash, peerHash]) => {
    const announceToTracker = async (tracker, index) => {
      const interval = await announceToTracker(tracker, roomHash, peerHash);
      
      if (typeof interval === 'number') {
        trackerUpdateIntervals[index] = interval;
      }
      
      trackerTimeouts[index] = setTimeout(
        () => announceToTracker(tracker, index),
        trackerUpdateIntervals[index]
      );
    };

    trackerSubscriptions.forEach(async (subscription, index) => {
      await subscription;
      announceToTracker(await trackers[index], index);
    });
  });

  // Handler for new connections
  let connectionHandler = () => {};

  // Create signal handler for peer connections
  function createSignalHandler(trackerId) {
    return async (roomHash, message, sendResponse) => {
      // Ignore messages not for this room
      const [expectedRoomHash, expectedSelfHash] = await Promise.all([namespaceHash, selfHash]);
      if (roomHash !== expectedRoomHash && roomHash !== expectedSelfHash) return;

      // Parse the message
      const { peerId, offer, answer, peer } = 
        typeof message === 'string' ? JSON.parse(message) : message;

      // Ignore self messages and handle only those with offers/answers
      if (peerId !== SELF_ID && !pendingConnections[peerId]) {
        if (!peerId || offer || answer) {
          // Handle incoming offer
          if (offer) {
            const existingConn = pendingConnections[peerId]?.[trackerId];
            
            // Skip if we already have a connection and our ID is higher (tie-breaker)
            if (existingConn && SELF_ID > peerId) return;
            
            // Create a new connection as the receiver
            const newConn = createPeerConnection(false, config);
            
            // Set up handlers
            newConn.setHandlers({
              connect() {
                registerPeer(newConn, peerId, trackerId);
              },
              close() {
                unregisterPeer(newConn, peerId);
              }
            });
            
            // Decrypt and process the offer
            try {
              const decryptedOffer = await decryptSignal(offer);
              if (newConn.isDead) return;
              
              // Send answer back
              const [peerPathHash, answer] = await Promise.all([
                getHash(joinPaths(namespace, peerId)),
                newConn.signal(decryptedOffer)
              ]);
              
              const encryptedAnswer = await encryptSignal(answer);
              sendResponse(peerPathHash, JSON.stringify({
                peerId: SELF_ID,
                answer: encryptedAnswer
              }));
              
            } catch (err) {
              // Handle decryption errors (likely wrong password)
              onIncorrectPassword(peerId, 'offer');
              return;
            }
          } 
          // Handle incoming answer
          else if (answer) {
            try {
              const decryptedAnswer = await decryptSignal(answer);
              
              // Apply answer to the correct peer
              if (peer) {
                peer.setHandlers({
                  connect() {
                    registerPeer(peer, peerId, trackerId);
                  },
                  close() {
                    unregisterPeer(peer, peerId);
                  }
                });
                peer.signal(decryptedAnswer);
              } else {
                // Try to find an existing connection attempt
                const existingConn = pendingConnections[peerId]?.[trackerId];
                if (existingConn && !existingConn.isDead) {
                  existingConn.signal(decryptedAnswer);
                }
              }
            } catch (err) {
              onIncorrectPassword(peerId, 'answer');
              return;
            }
          }
        } 
        // Handle peer discovery (create offer)
        else {
          // Skip if we already have a pending connection
          if (pendingConnections[peerId]?.[trackerId]) return;
          
          // Create a new offer
          const [[{ peer: newPeer, offer }], peerPathHash] = await Promise.all([
            createOfferBatch(1),
            getHash(joinPaths(namespace, peerId))
          ]);
          
          // Register as pending
          if (!pendingConnections[peerId]) {
            pendingConnections[peerId] = {};
          }
          pendingConnections[peerId][trackerId] = newPeer;
          
          // Set timeout to clean up if no response
          setTimeout(() => {
            cleanupPendingConnection(peerId, trackerId);
          }, trackerUpdateIntervals[trackerId] * 0.9);
          
          // Setup handlers
          newPeer.setHandlers({
            connect() {
              registerPeer(newPeer, peerId, trackerId);
            },
            close() {
              unregisterPeer(newPeer, peerId);
            }
          });
          
          // Send offer
          sendResponse(peerPathHash, JSON.stringify({
            peerId: SELF_ID,
            offer
          }));
        }
      }
    };
  }

  /**
   * Creates a batch of WebRTC offers
   * @param {number} count - Number of offers to create
   * @returns {Promise<Array>} Array of peer and offer pairs
   */
  function createOfferBatch(count) {
    // Add new peer connections to the pending list
    peerConnections.push(...Array(count).fill().map(() => 
      createPeerConnection(true, config)
    ));
    
    // Get offers from the connections
    return Promise.all(
      peerConnections.splice(0, count).map(peer => 
        peer.offerPromise
          .then(encryptSignal)
          .then(offer => ({ peer, offer }))
      )
    );
  }

  /**
   * Register a peer connection
   * @param {Object} connection - WebRTC peer connection
   * @param {string} peerId - ID of the peer
   * @param {number} trackerId - Index of the tracker
   */
  function registerPeer(connection, peerId, trackerId) {
    // If already connected to this peer via another connection, keep the
    // current connection only if it's the same peer
    if (peers[peerId]) {
      if (peers[peerId] !== connection) {
        connection.destroy();
      }
      return;
    }
    
    // Register the peer
    peers[peerId] = connection;
    
    // Pass connection to handler function
    connectionHandler(connection, peerId);
    
    // Clean up any pending connections with this peer
    if (pendingConnections[peerId]) {
      Object.entries(pendingConnections[peerId]).forEach(([id, conn]) => {
        if (id !== trackerId.toString()) {
          conn.destroy();
        }
      });
      delete pendingConnections[peerId];
    }
  }

  /**
   * Unregister a peer connection
   * @param {Object} connection - WebRTC peer connection
   * @param {string} peerId - ID of the peer
   */
  function unregisterPeer(connection, peerId) {
    if (peers[peerId] === connection) {
      delete peers[peerId];
    }
  }

  /**
   * Clean up a pending connection
   * @param {string} peerId - ID of the peer
   * @param {number} trackerId - Index of the tracker
   */
  function cleanupPendingConnection(peerId, trackerId) {
    if (!peers[peerId]) {
      const pendingConn = pendingConnections[peerId]?.[trackerId];
      if (pendingConn) {
        delete pendingConnections[peerId][trackerId];
        pendingConn.destroy();
      }
    }
  }

  /**
   * Handle incorrect password
   * @param {string} peerId - ID of the peer
   * @param {string} messageType - Type of message
   */
  function onIncorrectPassword(peerId, messageType) {
    onSignal?.({
      error: `incorrect password (${config.password}) when decrypting ${messageType}`,
      appId,
      peerId,
      roomId
    });
  }

  // Create the room interface
  roomRegistry[appId][roomId] = createRoomInterface(
    (handler) => connectionHandler = handler,
    (peerId) => delete hashCache[peerId],
    () => {
      // Clean up when leaving the room
      delete roomRegistry[appId][roomId];
      trackerTimeouts.forEach(clearTimeout);
      trackerSubscriptions.forEach(async (sub) => (await sub)());
      clearInterval(peerConnectionCleanupInterval);
    }
  );

  // Set up regular cleanup of stale peer connections
  const peerConnectionCleanupInterval = setInterval(() => {
    peerConnections = peerConnections.filter(peer => {
      const isValid = Date.now() - peer.created < 57333;
      if (!isValid) {
        peer.destroy();
      }
      return isValid;
    });
  }, 59052.99);

  /**
   * Create the room interface with all available methods
   * @param {Function} setConnectionHandler - Function to set the connection handler
   * @param {Function} removePeerHash - Function to remove a peer hash
   * @param {Function} cleanupRoom - Function to clean up room resources
   * @returns {Object} Room interface
   */
  function createRoomInterface(setConnectionHandler, removePeerHash, cleanupRoom) {
    // Action registry
    const actions = {};
    const actionTypes = {};
    const actionMetadata = {};
    const peerStreamMetadata = {};
    const peerTrackMetadata = {};
    
    // Callbacks
    const callbacks = {
      onPeerJoin: () => {},
      onPeerLeave: () => {},
      onPeerStream: () => {},
      onPeerTrack: () => {}
    };

    // Create a special action type with system prefix
    const systemPrefix = '@_';
    function createSystemAction(name) {
      return createAction(systemPrefix + name);
    }

    // Setup basic system actions
    const [pingAction, pingHandler] = createSystemAction('ping');
    const [pongAction, pongHandler] = createSystemAction('pong');
    const [signalAction, signalHandler] = createSystemAction('signal');
    const [streamAction, streamHandler] = createSystemAction('stream');
    const [trackAction, trackHandler] = createSystemAction('track');
    const [leaveAction, leaveHandler] = createSystemAction('leave');

    // Set up connection handler
    setConnectionHandler((connection, peerId) => {
      if (!peers[peerId]) {
        peers[peerId] = connection;
        
        connection.setHandlers({
          data: (data) => handleData(peerId, data),
          stream(stream) {
            callbacks.onPeerStream(stream, peerId, peerStreamMetadata[peerId]);
            delete peerStreamMetadata[peerId];
          },
          track(track, stream) {
            callbacks.onPeerTrack(track, stream, peerId, peerTrackMetadata[peerId]);
            delete peerTrackMetadata[peerId];
          },
          signal: (signal) => signalAction(signal, peerId),
          close: () => removePeer(peerId),
          error: () => removePeer(peerId)
        });
        
        callbacks.onPeerJoin(peerId);
        
        // Process any early data
        connection.drainEarlyData?.(data => handleData(peerId, data));
      }
    });

    // Set up system action handlers
    pingHandler((_, peerId) => pongAction('', peerId));
    
    pongHandler((_, peerId) => {
      if (pingPromises[peerId]) {
        pingPromises[peerId]();
        delete pingPromises[peerId];
      }
    });
    
    signalHandler((signal, peerId) => peers[peerId]?.signal(signal));
    
    streamHandler((metadata, peerId) => peerStreamMetadata[peerId] = metadata);
    
    trackHandler((metadata, peerId) => peerTrackMetadata[peerId] = metadata);
    
    leaveHandler((_, peerId) => removePeer(peerId));

    // Set up beforeunload handler
    if (IS_BROWSER) {
      window.addEventListener('beforeunload', leaveRoom);
    }

    /**
     * Helper functions for the room interface
     */
    
    // Ping response tracking
    const pingPromises = {};

    /**
     * Remove a peer from the room
     * @param {string} peerId - ID of the peer to remove
     */
    function removePeer(peerId) {
      if (peers[peerId]) {
        delete peers[peerId];
        delete actionMetadata[peerId];
        callbacks.onPeerLeave(peerId);
        removePeerHash(peerId);
      }
    }

    /**
     * Handle incoming data from a peer
     * @param {string} peerId - ID of the peer
     * @param {ArrayBuffer} rawData - Raw data received
     */
    function handleData(peerId, rawData) {
      const data = new Uint8Array(rawData);
      
      // Extract message parts
      const actionType = decodeText(data.subarray(0, 12)).replaceAll('\0', '');
      const [sequenceNumber] = data.subarray(12, 13);
      const [flags] = data.subarray(13, 14);
      const [progress] = data.subarray(14, 15);
      const payload = data.subarray(15);
      
      // Parse flags
      const isFinalChunk = !!(flags & 1);
      const isMetadata = !!(flags & 2);
      const isBinary = !!(flags & 4);
      const isJson = !!(flags & 8);
      
      // Skip unknown action types
      if (!actions[actionType]) {
        console.warn(`${LIBRARY_NAME}: received message with unregistered type (${actionType})`);
        return;
      }
      
      // Initialize message storage
      actionMetadata[peerId] ||= {};
      actionMetadata[peerId][actionType] ||= {};
      
      const messageState = actionMetadata[peerId][actionType][sequenceNumber] || { chunks: [] };
      
      // Store metadata or chunk
      if (isMetadata) {
        messageState.meta = JSON.parse(decodeText(payload));
      } else {
        messageState.chunks.push(payload);
      }
      
      // Report progress
      actions[actionType].onProgress(progress / PROGRESS_MAX, peerId, messageState.meta);
      
      // Process complete message
      if (isFinalChunk) {
        // Combine chunks
        const totalSize = messageState.chunks.reduce((sum, chunk) => sum + chunk.byteLength, 0);
        const combined = new Uint8Array(totalSize);
        
        messageState.chunks.reduce((offset, chunk) => {
          combined.set(chunk, offset);
          return offset + chunk.byteLength;
        }, 0);
        
        // Clean up
        delete actionMetadata[peerId][actionType][sequenceNumber];
        
        // Process based on type
        if (isBinary) {
          actions[actionType].onComplete(combined, peerId, messageState.meta);
        } else {
          const textData = decodeText(combined);
          actions[actionType].onComplete(
            isJson ? JSON.parse(textData) : textData,
            peerId
          );
        }
      }
    }

    /**
     * Create a new action type
     * @param {string} actionType - Type identifier for the action
     * @returns {Array} [sendFunction, setCompleteHandler, setProgressHandler]
     */
    function createAction(actionType) {
      // Return existing action if already created
      if (actionTypes[actionType]) {
        return actionTypes[actionType];
      }
      
      // Validate action type
      if (!actionType) {
        throw createError('action type argument is required');
      }
      
      const actionBytes = encodeText(actionType);
      if (actionBytes.byteLength > 12) {
        throw createError(
          `action type string "${actionType}" (${actionBytes.byteLength}b) exceeds byte limit (12). ` +
          'Hint: choose a shorter name.'
        );
      }
      
      // Create action header (12 bytes for type)
      const header = new Uint8Array(12);
      header.set(actionBytes);
      
      // Initialize sequence counter
      let sequenceCounter = 0;
      
      // Create action interface
      const actionInterface = {
        onComplete: () => {},
        onProgress: () => {},
        
        setOnComplete(handler) {
          actionInterface.onComplete = handler;
          return actionInterface;
        },
        
        setOnProgress(handler) {
          actionInterface.onProgress = handler;
          return actionInterface;
        },
        
        /**
         * Send data to peers
         * @param {*} data - Data to send
         * @param {string|string[]} [target] - Target peer(s)
         * @param {Object} [meta] - Metadata to include
         * @param {Function} [progressCallback] - Progress callback
         */
        async send(data, target, meta, progressCallback) {
          // Validate inputs
          if (meta && typeof meta !== 'object') {
            throw createError('action meta argument must be an object');
          }
          
          const dataType = typeof data;
          if (dataType === 'undefined') {
            throw createError('action data cannot be undefined');
          }
          
          // Determine data format
          const isNotString = dataType !== 'string';
          const isBlob = data instanceof Blob;
          const isBinary = isBlob || data instanceof ArrayBuffer || 
                          data instanceof Object.getPrototypeOf(Uint8Array);
          
          // Validate metadata use
          if (meta && !isBinary) {
            throw createError('action meta argument can only be used with binary data');
          }
          
          // Convert data to binary
          let binaryData;
          if (isBinary) {
            binaryData = isBlob 
              ? new Uint8Array(await data.arrayBuffer()) 
              : new Uint8Array(data);
          } else {
            binaryData = encodeText(isNotString ? JSON.stringify(data) : data);
          }
          
          // Convert metadata to binary if present
          const metaBinary = meta ? encodeText(JSON.stringify(meta)) : null;
          
          // Calculate chunks
          const chunkCount = Math.ceil(binaryData.byteLength / MAX_CHUNK_SIZE) + 
                           (meta ? 1 : 0) || 1;
          
          // Prepare chunks
          const chunks = Array(chunkCount).fill().map((_, index) => {
            const isLastChunk = index === chunkCount - 1;
            const isMetaChunk = meta && index === 0;
            
            // Calculate payload size and offset
            let payloadSize, payloadOffset;
            if (isMetaChunk) {
              payloadSize = metaBinary.byteLength;
            } else if (isLastChunk) {
              const dataIndex = index - (meta ? 1 : 0);
              payloadOffset = dataIndex * MAX_CHUNK_SIZE;
              payloadSize = binaryData.byteLength - payloadOffset;
            } else {
              const dataIndex = index - (meta ? 1 : 0);
              payloadOffset = dataIndex * MAX_CHUNK_SIZE;
              payloadSize = MAX_CHUNK_SIZE;
            }
            
            // Create chunk header
            const chunk = new Uint8Array(15 + payloadSize);
            
            // Set header fields
            chunk.set(header);  // Action type (12 bytes)
            chunk.set([sequenceCounter], 12);  // Sequence number (1 byte)
            
            // Flags (1 byte):
            // - Bit 0: Is final chunk
            // - Bit 1: Is metadata
            // - Bit 2: Is binary
            // - Bit 3: Is JSON
            const flags = (isLastChunk ? 1 : 0) | 
                         (isMetaChunk ? 2 : 0) | 
                         (isBinary ? 4 : 0) | 
                         (isNotString ? 8 : 0);
            chunk.set([flags], 13);
            
            // Progress (1 byte)
            chunk.set([Math.round((index + 1) / chunkCount * PROGRESS_MAX)], 14);
            
            // Set payload
            if (isMetaChunk) {
              chunk.set(metaBinary, 15);
            } else {
              chunk.set(
                binaryData.subarray(
                  payloadOffset,
                  payloadOffset + payloadSize
                ),
                15
              );
            }
            
            return chunk;
          });
          
          // Increment sequence counter (and wrap around)
          sequenceCounter = (sequenceCounter + 1) & PROGRESS_MAX;
          
          // Send to targets
          return Promise.all(
            forEachPeer(target, async (peerId, connection) => {
              const { channel } = connection;
              let sentChunks = 0;
              
              while (sentChunks < chunkCount) {
                const chunk = chunks[sentChunks];
                
                // Handle buffer overflow
                if (channel.bufferedAmount > channel.bufferedAmountLowThreshold) {
                  await new Promise(resolve => {
                    const handler = () => {
                      channel.removeEventListener(BUFFER_LOW_EVENT, handler);
                      resolve();
                    };
                    channel.addEventListener(BUFFER_LOW_EVENT, handler);
                  });
                }
                
                // Check if peer is still connected
                if (!peers[peerId]) break;
                
                // Send chunk
                connection.sendData(chunk);
                sentChunks++;
                
                // Report progress
                progressCallback?.(chunk[14] / PROGRESS_MAX, peerId, meta);
              }
            })
          );
        }
      };
      
      // Register and return
      actions[actionType] = actionInterface;
      actionTypes[actionType] = [
        actionInterface.send,
        actionInterface.setOnComplete,
        actionInterface.setOnProgress
      ];
      
      return actionTypes[actionType];
    }

    /**
     * Apply a function to each target peer
     * @param {string|string[]} [targets] - Target peer(s)
     * @param {Function} fn - Function to apply
     * @returns {Array} Results
     */
    function forEachPeer(targets, fn) {
      // Use all peers if no targets specified
      const peerIds = targets 
        ? (Array.isArray(targets) ? targets : [targets])
        : Object.keys(peers);
      
      return peerIds.flatMap(peerId => {
        const peer = peers[peerId];
        return peer 
          ? fn(peerId, peer)
          : (console.warn(`${LIBRARY_NAME}: no peer with id ${peerId} found`), []);
      });
    }

    /**
     * Leave the room and clean up resources
     */
    async function leaveRoom() {
      await getHash(''); // Ensure hash cache is ready
      
      // Close all connections
      Object.entries(peers).forEach(([peerId, connection]) => {
        connection.destroy();
        delete peers[peerId];
        delete actionMetadata[peerId];
        callbacks.onPeerLeave(peerId);
      });
      
      // Clean up room
      cleanupRoom();
    }

    // Return the room interface
    return {
      // Core actions
      makeAction: createAction,
      leave: leaveRoom,
      
      // Peer methods
      async ping(peerId) {
        if (!peerId) {
          throw createError('ping() must be called with target peer ID');
        }
        
        const startTime = Date.now();
        pingAction('', peerId);
        
        await new Promise(resolve => {
          pingPromises[peerId] = resolve;
        });
        
        return Date.now() - startTime;
      },
      
      getPeers() {
        return Object.fromEntries(
          Object.entries(peers).map(([id, peer]) => [id, peer.connection])
        );
      },
      
      // Media methods
      addStream: (stream, targets, metadata) => 
        forEachPeer(targets, async (peerId, peer) => {
          if (metadata) await streamAction(metadata, peerId);
          peer.addStream(stream);
        }),
        
      removeStream: (stream, targets) => 
        forEachPeer(targets, (peerId, peer) => 
          peer.removeStream(stream)
        ),
        
      addTrack: (track, stream, targets, metadata) => 
        forEachPeer(targets, async (peerId, peer) => {
          if (metadata) await trackAction(metadata, peerId);
          peer.addTrack(track, stream);
        }),
        
      removeTrack: (track, targets) => 
        forEachPeer(targets, (peerId, peer) => 
          peer.removeTrack(track)
        ),
        
      replaceTrack: (oldTrack, newTrack, stream, targets, metadata) => 
        forEachPeer(targets, async (peerId, peer) => {
          if (metadata) await trackAction(metadata, peerId);
          peer.replaceTrack(oldTrack, newTrack, stream);
        }),
      
      // Event handlers
      onPeerJoin: handler => callbacks.onPeerJoin = handler,
      onPeerLeave: handler => callbacks.onPeerLeave = handler,
      onPeerStream: handler => callbacks.onPeerStream = handler,
      onPeerTrack: handler => callbacks.onPeerTrack = handler
    };
  }

  return roomRegistry[appId][roomId];
}

/**
 * Initialize WebRTC peer connection
 * @param {boolean} isInitiator - Whether this peer initiates the connection
 * @param {Object} config - Configuration options
 * @returns {Object} Peer connection interface
 */
function createPeerConnection(isInitiator, config) {
  const { rtcConfig, rtcPolyfill, turnConfig } = config;
  
  // Create RTCPeerConnection with configuration
  const connection = new (rtcPolyfill || RTCPeerConnection)({
    iceServers: defaultIceServers.concat(turnConfig || []),
    ...rtcConfig
  });
  
  // Event handlers
  const handlers = {};
  
  // Data channel
  let dataChannel = null;
  let isNegotiating = false;
  let isDead = false;
  
  // Set up data channel
  function setupDataChannel(channel) {
    channel.binaryType = 'arraybuffer';
    channel.bufferedAmountLowThreshold = 65535;
    
    channel.onmessage = event => handlers.data?.(event.data);
    channel.onopen = () => handlers.connect?.();
    channel.onclose = () => handlers.close?.();
    channel.onerror = event => handlers.error?.(event);
  }
  
  // If initiator, create data channel
  if (isInitiator) {
    dataChannel = connection.createDataChannel('data');
    setupDataChannel(dataChannel);
  } else {
    // Otherwise wait for other peer to create it
    connection.ondatachannel = ({ channel }) => {
      dataChannel = channel;
      setupDataChannel(channel);
    };
  }
  
  // Handle ICE gathering completion
  async function getCompleteDescription(pc) {
    if (!pc.localDescription) {
      throw Error('No local description available');
    }
    
    // Wait for ICE gathering to complete or timeout
    await Promise.race([
      new Promise(resolve => {
        const checkState = () => {
          if (pc.iceGatheringState === 'complete') {
            pc.removeEventListener('icegatheringstatechange', checkState);
            resolve();
          }
        };
        pc.addEventListener('icegatheringstatechange', checkState);
        checkState();
      }),
      new Promise(resolve => setTimeout(resolve, 5000))
    ]);
    
    return {
      type: pc.localDescription.type,
      sdp: removeTrickleOption(pc.localDescription.sdp)
    };
  }
  
  // Remove trickle option from SDP
  function removeTrickleOption(sdp) {
    return sdp.replace(/a=ice-options:trickle\s\n/g, '');
  }
  
  // Handle negotiation
  connection.onnegotiationneeded = async () => {
    try {
      isNegotiating = true;
      await connection.setLocalDescription();
      
      const description = await getCompleteDescription(connection);
      handlers.signal?.({
        type: description.type,
        sdp: removeTrickleOption(description.sdp)
      });
    } catch (error) {
      handlers.error?.(error);
    } finally {
      isNegotiating = false;
    }
  };
  
  // Handle connection state changes
  connection.onconnectionstatechange = () => {
    if (['disconnected', 'failed', 'closed'].includes(connection.connectionState)) {
      handlers.close?.();
    }
  };
  
  // Handle media
  connection.ontrack = event => {
    handlers.track?.(event.track, event.streams[0]);
    handlers.stream?.(event.streams[0]);
  };
  
  connection.onremovestream = event => {
    handlers.stream?.(event.stream, { removed: true });
  };
  
  // Start negotiation if we're the initiator and can't trickle
  if (isInitiator && !connection.canTrickleIceCandidates) {
    connection.onnegotiationneeded();
  }
  
  return {
    created: Date.now(),
    connection,
    
    get channel() {
      return dataChannel;
    },
    
    get isDead() {
      return connection.connectionState === 'closed';
    },
    
    // Handle signaling messages
    async signal(signalData) {
      if (dataChannel?.readyState !== 'open') {
        try {
          if (signalData.type === 'offer') {
            // Avoid collision with ongoing negotiations
            if ((isNegotiating || connection.signalingState !== 'stable') && 
                (isDead = !isInitiator, isDead)) {
              return;
            }
            
            await connection.setRemoteDescription(signalData);
            await connection.setLocalDescription();
            
            const description = await getCompleteDescription(connection);
            const sdp = removeTrickleOption(description.sdp);
            
            // Send answer
            handlers.signal?.({
              type: description.type,
              sdp
            });
            
            return {
              type: description.type,
              sdp
            };
          } 
          else if (signalData.type === 'answer' && 
                  (connection.signalingState === 'have-local-offer' || 
                   connection.signalingState === 'have-remote-offer')) {
            await connection.setRemoteDescription(signalData);
          }
        } catch (error) {
          handlers.error?.(error);
        }
      } 
      else if (signalData.type === 'offer' || connection.signalingState !== 'stable') {
        await connection.setRemoteDescription(signalData);
        
        if (signalData.type === 'offer') {
          await connection.setLocalDescription();
          const description = await getCompleteDescription(connection);
          
          handlers.signal?.({
            type: description.type,
            sdp: description.sdp
          });
          
          return {
            type: description.type,
            sdp: description.sdp
          };
        }
      }
    },
    
    // Send data through the channel
    sendData(data) {
      return dataChannel.send(data);
    },
    
    // Clean up connection
    destroy() {
      if (dataChannel) dataChannel.close();
      connection.close();
    },
    
    // Set event handlers
    setHandlers(newHandlers) {
      return Object.assign(handlers, newHandlers);
    },
    
    // Offer promise for initiators
    offerPromise: isInitiator 
      ? new Promise(resolve => {
          handlers.signal = signal => {
            if (signal.type === 'offer') resolve(signal);
          };
        })
      : Promise.resolve(),
    
    // Media stream methods
    addStream(stream) {
      stream.getTracks().forEach(track => 
        connection.addTrack(track, stream)
      );
    },
    
    removeStream(stream) {
      connection.getSenders()
        .filter(sender => stream.getTracks().includes(sender.track))
        .forEach(sender => connection.removeTrack(sender));
    },
    
    addTrack(track, stream) {
      return connection.addTrack(track, stream);
    },
    
    removeTrack(track) {
      const sender = connection.getSenders().find(s => s.track === track);
      if (sender) connection.removeTrack(sender);
    },
    
    async replaceTrack(oldTrack, newTrack) {
      const sender = connection.getSenders().find(s => s.track === oldTrack);
      if (sender) await sender.replaceTrack(newTrack);
    }
  };
}

/**
 * Initialize WebTorrent trackers
 * @param {Object} config - Configuration options
 * @returns {Array} Array of tracker promises
 */
function initializeTrackers(config) {
  // Select trackers based on configuration
  const trackerUrls = config.relayUrls || DEFAULT_TRACKER_URLS;
  const redundancy = config.relayUrls 
    ? config.relayUrls.length 
    : (config.relayRedundancy || DEFAULT_RELAY_REDUNDANCY);
  
  // Use only the specified number of trackers
  return trackerUrls.slice(0, redundancy).map(url => {
    // Reuse existing tracker connection
    if (trackerSockets[url]) {
      return trackerSockets[url].ready;
    }
    
    // Create new tracker connection
    const tracker = createTrackerConnection(url, handleTrackerMessage);
    
    // Store for reuse
    trackerHandlers[url] = {};
    trackerSockets[url] = tracker;
    
    return tracker.ready;
  });
}

/**
 * Create connection to WebTorrent tracker
 * @param {string} url - Tracker WebSocket URL
 * @param {Function} messageHandler - Function to handle messages
 * @returns {Object} Tracker connection
 */
function createTrackerConnection(url, messageHandler) {
  const tracker = {};
  
  // Initialize reconnection delay
  reconnectTimes[url] ??= 3333;
  
  // Connect to tracker
  function connect() {
    const socket = new WebSocket(url);
    
    // Handle connection close
    socket.onclose = () => {
      // Exponential backoff for reconnection
      setTimeout(connect, reconnectTimes[url]);
      reconnectTimes[url] *= 2;
    };
    
    // Handle incoming messages
    socket.onmessage = event => messageHandler(event.data);
    
    // Store socket reference
    tracker.socket = socket;
    tracker.url = socket.url;
    
    // Create ready promise
    tracker.ready = new Promise(resolve => {
      socket.onopen = () => {
        resolve(tracker);
        reconnectTimes[url] = 3333;
      };
    });
    
    // Send method that checks socket state
    tracker.send = data => {
      if (socket.readyState === 1) {
        socket.send(data);
      }
    };
  }
  
  // Start connection
  connect();
  
  return tracker;
}

/**
 * Handle tracker message
 * @param {string} message - Message from tracker
 */
function handleTrackerMessage(message) {
  const data = JSON.parse(message);
  
  // Check for error
  const failure = data['failure reason'];
  const warning = data['warning message'];
  const { interval } = data;
  const roomId = hashCache[data.info_hash];
  
  if (failure) {
    console.warn(`${LIBRARY_NAME}: torrent tracker failure from ${url} - ${failure}`);
    return;
  }
  
  if (warning) {
    console.warn(`${LIBRARY_NAME}: torrent tracker warning from ${url} - ${warning}`);
  }
  
  // Update announcement interval if necessary
  if (interval && interval * 1000 > trackerDefaultInterval && trackerAnnouncers[url]?.[roomId]) {
    const newInterval = Math.min(interval * 1000, 120333);
    clearInterval(roomTrackerIntervals[url][roomId]);
    trackerDefaultInterval = newInterval;
    roomTrackerIntervals[url][roomId] = setInterval(trackerAnnouncers[url][roomId], newInterval);
  }
  
  // Handle offer/answer
  if (!pendingOffers[data.offer_id] && (data.offer || data.answer)) {
    pendingOffers[data.offer_id] = true;
    trackerHandlers[url][roomId]?.(data);
  }
}

/**
 * Subscribe to tracker for a room
 * @param {Object} tracker - Tracker connection
 * @param {string} roomHash - Room hash
 * @param {string} peerHash - Peer hash
 * @param {Function} signalHandler - Signal handler
 * @param {Function} createOffers - Function to create offers
 * @returns {Function} Unsubscribe function
 */
async function subscribeToTracker(tracker, roomHash, peerHash, signalHandler, createOffers) {
  const { url } = tracker;
  
  // Create announcement function
  const announce = async () => {
    // Create offers for new peers
    const offers = Object.fromEntries(
      (await createOffers(10)).map(offer => [generateRandomId(20), offer])
    );
    
    // Set up handler for this room
    trackerHandlers[url][roomHash] = data => {
      if (data.offer) {
        // Handle incoming offer
        signalHandler(
          roomHash,
          { offer: data.offer, peerId: data.peer_id },
          (responseHash, response) => {
            announceToTracker(tracker, roomHash, {
              answer: JSON.parse(response).answer,
              offer_id: data.offer_id,
              to_peer_id: data.peer_id
            });
          }
        );
      } else if (data.answer) {
        // Handle incoming answer
        const pendingOffer = offers[data.offer_id];
        if (pendingOffer) {
          signalHandler(
            roomHash, 
            { answer: data.answer, peerId: data.peer_id, peer: pendingOffer.peer }
          );
        }
      }
    };
    
    // Send offers to tracker
    announceToTracker(tracker, roomHash, {
      numwant: 10,
      offers: Object.entries(offers).map(([offerId, { offer }]) => ({
        offer_id: offerId,
        offer
      }))
    });
  };
  
  // Set up storage if not exists
  trackerDefaultInterval = 33333;
  trackerAnnouncers[url] ||= {};
  trackerAnnouncers[url][roomHash] = announce;
  
  roomTrackerIntervals[url] ||= {};
  roomTrackerIntervals[url][roomHash] = setInterval(announce, trackerDefaultInterval);
  
  // Initial announcement
  await announce();
  
  // Return unsubscribe function
  return () => {
    clearInterval(roomTrackerIntervals[url][roomHash]);
    delete trackerHandlers[url][roomHash];
    delete trackerAnnouncers[url][roomHash];
  };
}

/**
 * Announce to tracker
 * @param {Object} tracker - Tracker connection
 * @param {string} roomHash - Room hash
 * @param {Object} data - Data to announce
 * @returns {number|undefined} New interval if provided by tracker
 */
function announceToTracker(tracker, roomHash, data = {}) {
  tracker.send(JSON.stringify({
    action: 'announce',
    info_hash: roomHash,
    peer_id: SELF_ID,
    ...data
  }));
  
  return trackerDefaultInterval;
}

/**
 * Get all relay socket connections
 * @returns {Object} Mapping of URL to WebSocket
 */
function getRelaySockets() {
  return Object.fromEntries(
    Object.entries(trackerSockets).map(([url, tracker]) => [url, tracker.socket])
  );
}

/**
 * Calculate hash of string
 * @param {string} input - String to hash
 * @returns {Promise<string>} Hash string
 */
async function getHash(input) {
  if (hashCache[input]) {
    return hashCache[input];
  }
  
  // Calculate SHA-1 hash
  const buffer = await crypto.subtle.digest('SHA-1', encodeText(input));
  
  // Convert to string
  const hash = Array.from(new Uint8Array(buffer))
    .map(byte => byte.toString(36))
    .join('');
  
  // Cache and return truncated hash
  const truncatedHash = hash.slice(0, 20);
  hashCache[input] = truncatedHash;
  return truncatedHash;
}

/**
 * Join paths with separator
 * @param  {...string} parts - Path parts
 * @returns {string} Joined path
 */
function joinPaths(...parts) {
  return parts.join('@');
}

/**
 * Derive encryption key from password and context
 * @param {string} password - Password string
 * @param {string} appId - Application ID
 * @param {string} roomId - Room ID
 * @returns {Promise<CryptoKey>} Encryption key
 */
async function deriveEncryptionKey(password, appId, roomId) {
  // Create key material from context
  const keyMaterial = await crypto.subtle.digest(
    { name: 'SHA-256' },
    encodeText(`${password}:${appId}:${roomId}`)
  );
  
  // Import as AES-GCM key
  return crypto.subtle.importKey(
    'raw',
    keyMaterial,
    { name: CRYPTO_ALGORITHM },
    false,
    ['encrypt', 'decrypt']
  );
}

/**
 * Encrypt SDP with AES-GCM
 * @param {CryptoKey} key - Encryption key
 * @param {string} sdp - SDP to encrypt
 * @returns {Promise<string>} Encrypted string
 */
async function encryptSdp(key, sdp) {
  // Generate random initialization vector
  const iv = crypto.getRandomValues(new Uint8Array(16));
  
  // Encrypt SDP
  const encryptedBuffer = await crypto.subtle.encrypt(
    { name: CRYPTO_ALGORITHM, iv },
    key,
    encodeText(sdp)
  );
  
  // Convert to Base64
  const encryptedBase64 = btoa(
    String.fromCharCode.apply(null, new Uint8Array(encryptedBuffer))
  );
  
  // Return IV and encrypted data
  return `${iv.join(',')}${encryptedBase64}`;
}

/**
 * Decrypt SDP with AES-GCM
 * @param {CryptoKey} key - Decryption key
 * @param {string} encryptedSdp - Encrypted SDP
 * @returns {Promise<string>} Decrypted SDP
 */
async function decryptSdp(key, encryptedSdp) {
  // Split IV and data
  const [ivString, encryptedBase64] = encryptedSdp.split(');
  
  // Convert IV to Uint8Array
  const iv = new Uint8Array(ivString.split(','));
  
  // Convert Base64 to ArrayBuffer
  const encryptedBuffer = (() => {
    const binary = atob(encryptedBase64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) {
      bytes[i] = binary.charCodeAt(i);
    }
    return bytes.buffer;
  })();
  
  // Decrypt
  const decryptedBuffer = await crypto.subtle.decrypt(
    { name: CRYPTO_ALGORITHM, iv },
    key,
    encryptedBuffer
  );
  
  // Convert to string
  return decodeText(decryptedBuffer);
}

/**
 * Encode text to Uint8Array
 * @param {string} text - Text to encode
 * @returns {Uint8Array} Encoded bytes
 */
function encodeText(text) {
  return new TextEncoder().encode(text);
}

/**
 * Decode Uint8Array to text
 * @param {Uint8Array} bytes - Bytes to decode
 * @returns {string} Decoded text
 */
function decodeText(bytes) {
  return new TextDecoder().decode(bytes);
}

// Exports
export {
  DEFAULT_TRACKER_URLS as defaultRelayUrls,
  getRelaySockets,
  joinRoom,
  SELF_ID as selfId
};
