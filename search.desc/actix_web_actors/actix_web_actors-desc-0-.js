searchState.loadedDescShard("actix_web_actors", 0, "Actix actors support for Actix Web.\nExecution context for HTTP actors\nCreate a new HTTP Context from a request and an actor\nReturns the argument unchanged.\nHandle of the running future\nCalls <code>U::from(self)</code>.\nCreate a new HTTP Context\nWrite payload\nIndicate end of streaming payload. Also this method calls …\nWebsocket integration.\nIndicates an abnormal closure. If the abnormal closure was …\nIndicates that the server is overloaded and the client …\nIndicates that an endpoint is “going away”, such as a …\nBad opcode.\nWebSocket key is not set or wrong.\nBinary message.\nBinary frame.\nClose message with optional reason.\nClose message with optional reason.\nStatus code used to indicate why an endpoint is closing …\nReason for closing the connection\nContinuation.\nContinuation.\nUnknown continuation fragment.\nContinuation has not started.\nReceived new continuation but it is already started.\nIndicates that a server is terminating the connection …\nIndicates that an endpoint (client) is terminating the …\nA WebSocket frame.\nOnly get method is allowed.\nWebSocket handshake errors\nIndicates that an endpoint is terminating the connection …\nInvalid control frame length\nEncountered invalid opcode.\nI/O error.\nReceived a masked frame from server.\nA WebSocket message.\nConnection header is not set to upgrade.\nWebSocket version header is not set.\nUpgrade header if not set to WebSocket.\nNo-op. Useful for low-level services.\nIndicates a normal closure, meaning that the purpose for …\nA payload reached size limit.\nPing message.\nPing message.\nIndicates that an endpoint is terminating the connection …\nPong message.\nPong message.\nIndicates that an endpoint is terminating the connection …\nWebSocket protocol errors.\nIndicates that the server is restarting. A client may …\nIndicates that an endpoint is terminating the connection …\nText message.\nText frame. Note that the codec does not validate UTF-8 …\nReceived an unmasked frame from client.\nIndicates that an endpoint is terminating the connection …\nUnsupported WebSocket version.\nExecution context for <code>WebSockets</code> actors\nBuilder for Websocket session response.\nSend binary frame\nSend close frame\nExit code\nSet the <code>Codec</code> for the session. If <code>Self::frame_size</code> is also …\nCreate a new Websocket context from a request and an actor.\nCreate a new Websocket context from a request and an actor.\nOptional description of the exit code\nSet the max frame size for each message (in bytes).\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nHandle of the running future\nPrepare WebSocket handshake response.\nPrepare WebSocket handshake response.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nConstruct a new <code>WsResponseBuilder</code> with actor, request, and …\nSend ping frame\nSend pong frame\nSet the protocols for the session.\nSet mailbox capacity\nPerform WebSocket handshake and start actor.\nPerform WebSocket handshake and start actor.\nPerform WebSocket handshake and start actor.\nPerform WebSocket handshake and start actor.\nDo WebSocket handshake and start ws actor.\nSend text frame\nCreate a new Websocket context from a request, an actor, …\nCreate a new Websocket context\nWrite payload")