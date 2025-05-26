import pygame
import socket
import threading
import json
import sys
import random
import traceback
import time


class ScrabbleClient:
    # Class constants
    #TILE_SIZE = 40
    TILE_SIZE = 30
    BOARD_SIZE = 15
    MARGIN = 40
    RACK_HEIGHT = TILE_SIZE + 20
    INFO_HEIGHT = 60
    BUTTON_MARGIN = 10
    PLAYER_LIST_WIDTH = 200  # Width for player list
    WIDTH = TILE_SIZE * BOARD_SIZE + MARGIN * 2 + PLAYER_LIST_WIDTH + 20  # Added width for player list
    # Calculate button dimensions
    button_spacing = int(10 * (TILE_SIZE / 40))  # Scale spacing with tile size
    available_width = WIDTH - (2 * MARGIN)
    num_buttons = 6  # Total number of buttons
    total_spacing = button_spacing * (num_buttons - 1)
    button_width = (available_width - total_spacing) // num_buttons
    button_height = int(button_width * 0.35)  # Always 35% of button width
    HEIGHT = TILE_SIZE * BOARD_SIZE + MARGIN * 2 + RACK_HEIGHT + INFO_HEIGHT + button_height + BUTTON_MARGIN * 3 + 40  # slightly taller
    
    HOST = 'localhost'  # Default to localhost, will be overridden by user input
    PORT = 12345
    
    # Special tile colors
    SPECIAL_COLORS = {
        'DL': (173, 216, 230),
        'TL': (0, 191, 255),
        'DW': (255, 182, 193),
        'TW': (255, 99, 71),
        '*': (255, 215, 0),
    }
    
    # Letter tile colors
    LETTER_COLORS = {
        'placed': (255, 255, 255),      # White for server-confirmed letters
        'buffered': (255, 255, 150),    # Light yellow for client buffer
        'rack': (160, 160, 160),        # Gray for rack tiles
        'rack_selected': (200, 200, 200), # Lighter gray for selected rack
        'blank': (128, 0, 128),         # Dark purple for blank tiles
        'dragging': (180, 180, 180),    # Color for tile being dragged
    }
    
    # Letter colors
    LETTER_TEXT_COLORS = {
        'normal': (0, 0, 0),            # Black for normal letters
        'blank': (128, 0, 128),         # Dark purple for blank letters
    }
    
    # Special tile positions
    TRIPLE_WORD = [(0,0), (0,7), (0,14), (7,0), (7,14), (14,0), (14,7), (14,14)]
    DOUBLE_WORD = [(1,1), (2,2), (3,3), (4,4), (13,13), (12,12), (11,11), (10,10),
                   (1,13), (2,12), (3,11), (4,10), (13,1), (12,2), (11,3), (10,4),
                   (7,7)]
    TRIPLE_LETTER = [(1,5), (1,9), (5,1), (5,5), (5,9), (5,13),
                     (9,1), (9,5), (9,9), (9,13), (13,5), (13,9)]
    DOUBLE_LETTER = [(0,3), (0,11), (2,6), (2,8), (3,0), (3,7), (3,14),
                     (6,2), (6,6), (6,8), (6,12), (7,3), (7,11),
                     (8,2), (8,6), (8,8), (8,12), (11,0), (11,7), (11,14),
                     (12,6), (12,8), (14,3), (14,11)]
    
    # Standard Scrabble letter values
    LETTER_VALUES = {
        'A': 1, 'B': 3, 'C': 3, 'D': 2, 'E': 1, 'F': 4, 'G': 2, 'H': 4,
        'I': 1, 'J': 8, 'K': 5, 'L': 1, 'M': 3, 'N': 1, 'O': 1, 'P': 3,
        'Q': 10, 'R': 1, 'S': 1, 'T': 1, 'U': 1, 'V': 4, 'W': 4, 'X': 8,
        'Y': 4, 'Z': 10, '?': 0
    }
    
    # Input field colors
    INPUT_COLORS = {
        'background': (240, 240, 240),
        'border': (100, 100, 100),
        'border_active': (0, 120, 215),
        'text': (0, 0, 0),
        'placeholder': (150, 150, 150),
    }

    def __init__(self):
        """Initialize the Scrabble client."""
        pygame.init()
        self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
        pygame.display.set_caption("BAB GROUP SCRABBLE")
        
        # Initialize fonts
        self._update_font_sizes()
        
        self.clock = pygame.time.Clock()
        self.state_lock = threading.Lock()
        
        # Connection screen state
        self.connection_screen = True
        self.ip_input = ""
        self.username_input = ""
        self.active_input = "ip"  # Track which input is active
        self.error_message = None
        self.connecting = False
        
        # Game state
        self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
        self.tile_rack = []  # Will be populated from server
        self.selected_rack_index = None
        self.selected_board_cell = None
        self.tiles_remaining = 0  # Track tiles left in bag
        self.players = []  # Initialize players list
        self.exchange_mode = False  # Track if we're in exchange mode
        self.tiles_to_exchange = set()  # Track tiles selected for exchange
        
        # Drag state
        self.dragging_tile = False
        self.drag_start_index = None
        self.drag_current_index = None
        self.drag_offset = (0, 0)  # Offset from mouse position to tile center
        self.drag_start_pos = (0, 0)  # Starting position of drag
        self.drag_threshold = 5  # Minimum pixels to move before considering it a drag
        self.dragging_from_board = False  # Track if we're dragging from board
        self.drag_board_pos = None  # Track the board position we're dragging from
        
        # Game end state
        self.game_ended = False
        self.final_scores = {}
        self.winner = None
        
        # Blank tile handling
        self.blank_letter = None  # Track which letter was chosen for the blank
        self.blank_pos = None  # Track where the blank is being placed
        self.showing_blank_dialog = False  # Track if we're showing the blank letter dialog
        self.blank_tiles = set()  # Track positions of blank tiles in the buffer
        
        # Click tracking for double-click detection
        self.last_click_time = 0
        self.last_click_pos = None
        self.DOUBLE_CLICK_TIME = 300  # milliseconds
        
        # Dictionary for word validation
        self.dictionary = set()
        self._load_dictionary()
        
        # Move log
        self.move_log = []  # List of moves
        self.move_log_scroll = 0  # Scroll position for move log
        # Calculate height to end above buttons
        button_y = (self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 
                   self.RACK_HEIGHT + self.INFO_HEIGHT + 15 + 36 + 20)  # Button Y position
        log_y = self.MARGIN + 150  # Start of move log
        self.move_log_height = button_y - log_y - self.TILE_SIZE  # Height from log start to button area minus margin
        self.scroll_bar_rect = None  # Store scroll bar rectangle
        self.scroll_bar_dragging = False  # Track if scroll bar is being dragged
        self.scroll_bar_height = 0  # Height of the scroll bar
        self.scroll_bar_offset = 0  # Height between scroll bar and mouse
        self.move_log_content_height = 0
        
        # Client-side letter buffer - stores temporarily placed letters
        self.letter_buffer = {}  # {(row, col): letter}
        
        # Initialize special tiles
        self.special_tiles = self._initialize_special_tiles()
        
        # Button setup
        self._setup_buttons()
        
        # Network connection
        self.sock = None
        self.running = True  # Add running flag for shutdown
        self.network_thread = None
        self.ready = False  # Track if this client is ready
        self.game_started = False  # Track if game has started
        self.error_time = 0  # For auto-clearing error messages

        self.showing_unseen_tiles = False

    def _update_font_sizes(self):
        """Update font sizes based on current tile size."""
        # Base font sizes at tile size 40
        base_tile_size = 40
        scale_factor = self.TILE_SIZE / base_tile_size
        
        # Only scale the main font used for letters and special tiles
        self.font_size = int(24 * scale_factor)  # Main font for letters and special tiles
        self.score_font_size = int(16 * scale_factor)  # Score numbers for letter tiles
        self.button_font_size = int(30 * scale_factor)  # Button text - now scales with tile size
        
        # Fixed font sizes for other elements
        self.info_font_size = 18  # Info text
        self.title_font_size = 36  # Title text
        
        # Create font objects
        self.font = pygame.font.SysFont(None, self.font_size)
        self.score_font = pygame.font.SysFont(None, self.score_font_size)
        self.info_font = pygame.font.SysFont(None, self.info_font_size)
        self.button_font = pygame.font.SysFont(None, self.button_font_size)
        self.title_font = pygame.font.SysFont(None, self.title_font_size)

    def _initialize_special_tiles(self):
        """Initialize the special tiles grid."""
        special_tiles = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
        
        for r, c in self.TRIPLE_WORD:
            special_tiles[r][c] = 'TW'
        for r, c in self.DOUBLE_WORD:
            special_tiles[r][c] = 'DW'
        for r, c in self.TRIPLE_LETTER:
            special_tiles[r][c] = 'TL'
        for r, c in self.DOUBLE_LETTER:
            special_tiles[r][c] = 'DL'
        
        # Center tile is double word (no need for special '*' handling)
        special_tiles[7][7] = '*'
        
        return special_tiles

    def _setup_buttons(self):
        """Setup button rectangles and properties."""
        # Calculate Y position: below board, rack, info panel, error box, and spacings
        info_panel_height = self.INFO_HEIGHT
        error_box_height = 36
        spacing_above_error = 15  # space between info panel and error box
        spacing_below_error = 20  # space between error box and buttons
        button_y = (self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 
                   self.RACK_HEIGHT + info_panel_height + spacing_above_error + error_box_height + spacing_below_error)
        
        # Calculate button dimensions to span full width
        button_spacing = int(10 * (self.TILE_SIZE / 40))  # Scale spacing with tile size
        
        # Calculate available width (excluding margins)
        available_width = self.WIDTH - (2 * self.MARGIN)
        
        # Calculate button width to fit all buttons with spacing
        num_buttons = 6  # Total number of buttons
        total_spacing = button_spacing * (num_buttons - 1)
        button_width = (available_width - total_spacing) // num_buttons
        button_height = int(button_width * 0.35)  # Always 35% of button width
        
        # Create buttons with calculated dimensions
        self.return_button = pygame.Rect(
            self.MARGIN, 
            button_y, 
            button_width, 
            button_height
        )
        self.send_button = pygame.Rect(
            self.MARGIN + button_width + button_spacing, 
            button_y, 
            button_width, 
            button_height
        )
        self.exchange_button = pygame.Rect(
            self.MARGIN + 2 * (button_width + button_spacing),
            button_y,
            button_width,
            button_height
        )
        self.ready_button = pygame.Rect(
            self.MARGIN + 3 * (button_width + button_spacing),
            button_y,
            button_width,
            button_height
        )
        # Add shuffle button to the right of the pass button
        self.shuffle_button = pygame.Rect(
            self.MARGIN + 3 * (button_width + button_spacing),
            button_y,
            button_width,
            button_height
        )
        # Add pass button to the right of the ready button
        self.pass_button = pygame.Rect(
            self.MARGIN + 4 * (button_width + button_spacing),
            button_y,
            button_width,
            button_height
        )
        # Add unseen tiles button
        self.unseen_tiles_button = pygame.Rect(
            self.MARGIN + 5 * (button_width + button_spacing),
            button_y,
            button_width,
            button_height
        )

    def _draw_connection_screen(self):
        """Draw the connection screen with input fields."""
        # Clear screen
        self.screen.fill((255, 255, 255))
        
        # Draw title
        title = self.title_font.render("BAB GROUP SCRABBLE", True, (0, 0, 0))
        title_rect = title.get_rect(centerx=self.WIDTH // 2, y=self.MARGIN)
        self.screen.blit(title, title_rect)
        
        # Draw input fields
        input_width = 300
        input_height = 40
        input_x = (self.WIDTH - input_width) // 2
        input_y = self.MARGIN + 100
        
        # IP Address input
        ip_label = self.font.render("Server IP:", True, (0, 0, 0))
        self.screen.blit(ip_label, (input_x, input_y - 30))
        
        ip_rect = pygame.Rect(input_x, input_y, input_width, input_height)
        pygame.draw.rect(self.screen, self.INPUT_COLORS['background'], ip_rect)
        border_color = self.INPUT_COLORS['border_active'] if self.active_input == "ip" else self.INPUT_COLORS['border']
        pygame.draw.rect(self.screen, border_color, ip_rect, 2)
        
        ip_text = self.ip_input if self.ip_input else "localhost"
        text_color = self.INPUT_COLORS['text'] if self.ip_input else self.INPUT_COLORS['placeholder']
        ip_surface = self.font.render(ip_text, True, text_color)
        ip_text_rect = ip_surface.get_rect(midleft=(input_x + 10, input_y + input_height // 2))
        self.screen.blit(ip_surface, ip_text_rect)
        
        # Username input
        username_label = self.font.render("Username:", True, (0, 0, 0))
        self.screen.blit(username_label, (input_x, input_y + input_height + 20))
        
        username_rect = pygame.Rect(input_x, input_y + input_height + 50, input_width, input_height)
        pygame.draw.rect(self.screen, self.INPUT_COLORS['background'], username_rect)
        border_color = self.INPUT_COLORS['border_active'] if self.active_input == "username" else self.INPUT_COLORS['border']
        pygame.draw.rect(self.screen, border_color, username_rect, 2)
        
        username_text = self.username_input if self.username_input else "Enter username"
        text_color = self.INPUT_COLORS['text'] if self.username_input else self.INPUT_COLORS['placeholder']
        username_surface = self.font.render(username_text, True, text_color)
        username_text_rect = username_surface.get_rect(midleft=(input_x + 10, input_y + input_height + 50 + input_height // 2))
        self.screen.blit(username_surface, username_text_rect)
        
        # Connect button
        button_width = 200
        button_height = 40
        button_x = (self.WIDTH - button_width) // 2
        button_y = input_y + input_height * 2 + 100
        
        connect_rect = pygame.Rect(button_x, button_y, button_width, button_height)
        button_color = (100, 200, 100) if not self.connecting else (150, 150, 150)
        pygame.draw.rect(self.screen, button_color, connect_rect)
        pygame.draw.rect(self.screen, (0, 0, 0), connect_rect, 2)
        
        connect_text = "Connecting..." if self.connecting else "Connect"
        connect_surface = self.font.render(connect_text, True, (0, 0, 0))
        connect_text_rect = connect_surface.get_rect(center=connect_rect.center)
        self.screen.blit(connect_surface, connect_text_rect)
        
        # Draw error message if any
        if self.error_message:
            error_surface = self.font.render(self.error_message, True, (200, 0, 0))
            error_rect = error_surface.get_rect(centerx=self.WIDTH // 2, y=button_y + button_height + 20)
            self.screen.blit(error_surface, error_rect)
        
        # Store rectangles for click detection
        self.ip_rect = ip_rect
        self.username_rect = username_rect
        self.connect_rect = connect_rect

    def _handle_connection_screen_click(self, pos):
        """Handle clicks on the connection screen."""
        x, y = pos
        
        # Check which input field was clicked
        if self.ip_rect.collidepoint(x, y):
            self.active_input = "ip"
        elif self.username_rect.collidepoint(x, y):
            self.active_input = "username"
        elif self.connect_rect.collidepoint(x, y) and not self.connecting:
            self._attempt_connection()

    def _handle_connection_screen_key(self, event):
        """Handle keyboard input on the connection screen."""
        if event.key == pygame.K_TAB:
            # Switch between input fields
            self.active_input = "username" if self.active_input == "ip" else "ip"
        elif event.key == pygame.K_RETURN:
            # Try to connect
            if not self.connecting:
                self._attempt_connection()
        elif event.key == pygame.K_BACKSPACE:
            # Handle backspace
            if self.active_input == "ip":
                self.ip_input = self.ip_input[:-1]
            else:
                self.username_input = self.username_input[:-1]
        elif event.unicode.isprintable():
            # Add character to active input
            if self.active_input == "ip":
                if len(self.ip_input) < 15:  # Limit IP length
                    self.ip_input += event.unicode
            else:
                if len(self.username_input) < 20:  # Limit username length
                    self.username_input += event.unicode

    def _attempt_connection(self):
        """Attempt to connect to the server with the provided credentials."""
        if not self.username_input:
            self.error_message = "Please enter a username"
            self.error_time = pygame.time.get_ticks()  # Set error time when setting error
            return
            
        self.connecting = True
        self.error_message = None
        
        # Start connection in a separate thread to avoid blocking the UI
        threading.Thread(target=self._connect_to_server, daemon=True).start()

    def _connect_to_server(self):
        """Robust connection handling with timeout."""
        try:
            if self.sock:
                self.sock.close()
                self.sock = None
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            
            # Use the input from the connection screen
            server_ip = self.ip_input if self.ip_input else 'localhost'
            self.HOST = server_ip
            
            print(f"[DEBUG] Attempting to connect to {self.HOST}:{self.PORT}")
            try:
                # Set a short timeout for the initial connection
                self.sock.settimeout(10.0)
                self.sock.connect((self.HOST, self.PORT))
                print("[DEBUG] Socket connection successful")
                # After connection, set a longer timeout for user input
                self.sock.settimeout(None)  # No timeout for user input
                
                # Only proceed with username if connection is successful
                username = self.username_input
                print(f"[DEBUG] Sending username: {username}")
                # Set a timeout for the username response
                self.sock.settimeout(10.0)
                self.sock.sendall(f"USERNAME:{username}\n".encode())
                response = self._receive_line()
                print(f"[DEBUG] Server response: {response}")
                if response.startswith("ERROR"):
                    self.error_message = f"Server rejected connection: {response[6:]}"
                    self.error_time = pygame.time.get_ticks()  # Set error time when setting error
                    self.connecting = False
                    self._reset_game_state()
                    return
                elif response != "OK:Username accepted":
                    self.error_message = "Unexpected server response"
                    self.error_time = pygame.time.get_ticks()  # Set error time when setting error
                    self.connecting = False
                    self._reset_game_state()
                    return
                print("[DEBUG] Connected successfully! Waiting for game data...")
                # Store the username after successful connection
                self.username = username
                
                # Start network thread after successful connection and username acceptance
                if self.network_thread is None or not self.network_thread.is_alive():
                    self.network_thread = threading.Thread(target=self._receive_messages, daemon=True)
                    self.network_thread.start()
                    # Give the network thread a moment to start
                    time.sleep(0.1)
                
                # Connection successful, exit connection screen
                self.connection_screen = False
                self.connecting = False
                
            except ConnectionRefusedError:
                self.error_message = "Connection refused. Is the server running?"
                self.error_time = pygame.time.get_ticks()  # Set error time when setting error
                self.connecting = False
                self._reset_game_state()
                return
            except socket.gaierror:
                self.error_message = "Invalid IP address or hostname"
                self.error_time = pygame.time.get_ticks()  # Set error time when setting error
                self.connecting = False
                self._reset_game_state()
                return
            except Exception as e:
                self.error_message = f"Connection failed: {str(e)}"
                self.error_time = pygame.time.get_ticks()  # Set error time when setting error
                self.connecting = False
                self._reset_game_state()
                return
            
        except socket.timeout:
            self.error_message = "Connection timed out - is the server running?"
            self.connecting = False
            self._reset_game_state()
        except Exception as e:
            self.error_message = f"Connection failed: {str(e)}"
            self.connecting = False
            self._reset_game_state()

    def _receive_line(self):
        """Helper to read a complete line from socket."""
        buffer = []
        while True:
            try:
                chunk = self.sock.recv(1).decode()
                if not chunk:
                    break
                if chunk == '\n':
                    break
                buffer.append(chunk)
            except socket.timeout:
                print("Timeout while receiving data")
                break
            except Exception as e:
                print(f"Error receiving data: {e}")
                break
        return ''.join(buffer)

    def _receive_messages(self):
        """Network thread function to receive messages from server."""
        buffer = ""
        print("Network thread started - waiting for messages...")
        while self.running:
            if self.sock:
                try:
                    # Check if socket is actually connected before trying to receive
                    if not self.sock.getpeername():
                        print("Socket not connected, waiting...")
                        time.sleep(0.1)
                        continue
                        
                    data = self.sock.recv(4096).decode()
                    if not data:
                        print("Connection closed by server")
                        self._handle_server_disconnect("Server closed the connection")
                        break
                    buffer += data
                    while '\n' in buffer:
                        line, buffer = buffer.split('\n', 1)
                        line = line.strip()
                        print(f"[DEBUG] Received line: {repr(line)}")  # Debug print
                        if line:
                            try:
                                self._process_server_message(line)
                            except json.JSONDecodeError as e:
                                print(f"JSON decode error: {e}")
                                print(f"Raw message was: {repr(line)}")
                                if line.startswith("ERROR:"):
                                    print(f"Server error: {line[6:]}")
                                    if "shutting down" in line.lower():
                                        print("Server is shutting down, returning to connection screen...")
                                        self._handle_server_disconnect("Server is shutting down")
                                        return
                                elif line.startswith("OK:"):
                                    print(f"Server confirmation: {line[3:]}")
                            except Exception as e:
                                print(f"Error processing message: {e}")
                                print(f"Raw message was: {repr(line)}")
                except socket.timeout:
                    continue
                except ConnectionResetError:
                    print("Connection reset by server")
                    self._handle_server_disconnect("Connection reset by server")
                    break
                except Exception as e:
                    if self.running:
                        print(f"Network error: {e}")
                        self._handle_server_disconnect(f"Network error: {str(e)}")
                    break
            else:
                # If no socket, wait a bit before checking again
                time.sleep(0.1)

    def _handle_server_disconnect(self, error_message):
        """Handle server disconnection by returning to connection screen with error message."""
        print(f"Handling server disconnect: {error_message}")
        with self.state_lock:
            self._reset_game_state()
            self.error_message = error_message
            self.error_time = pygame.time.get_ticks()
            self.connection_screen = True

    def _process_server_message(self, message):
        """Process a message received from the server."""
        print(f"Processing message: {repr(message)}")
        try:
            message = message.strip()
            try:
                data = json.loads(message)
                print(f"Parsed JSON data: {data}")
                if isinstance(data, dict):
                    message_type = data.get("type")
                    if message_type == "game_end":
                        print("[DEBUG] Game end message received")
                        with self.state_lock:  # Acquire lock for state changes
                            print("[DEBUG] Acquired state lock for game end")
                            self.game_ended = True
                            print("[DEBUG] Set game_ended flag")
                            self.final_scores = data.get("scores", {})
                            print(f"[DEBUG] Final scores: {self.final_scores}")
                            # Safe winner calculation
                            if self.final_scores:
                                try:
                                    max_score = max(self.final_scores.values())
                                    winners = [k for k, v in self.final_scores.items() if v == max_score]
                                    self.winner = winners[0] if winners else None
                                    print(f"[DEBUG] Winner determined: {self.winner}")
                                except ValueError as e:
                                    print(f"[ERROR] Error calculating winner: {e}")
                                    self.winner = None
                            else:
                                print("[DEBUG] No final scores available")
                                self.winner = None
                            if self.sock:
                                try:
                                    self.sock.sendall("DISCONNECT\n".encode())
                                except:
                                    pass
                                # Finally close the socket
                                try:
                                    self.sock.close()
                                except:
                                    pass
                                self.sock = None
                    elif message_type == "players":
                        print("Received players update")
                        self.players = data["players"]
                        # Update game_started from server
                        if "game_started" in data:
                            self.game_started = data["game_started"]
                        # Update ready state based on server data
                        for player in self.players:
                            if player["username"] == self.username:
                                self.ready = player["ready"]
                                break
                        self.draw_player_list()
                    elif message_type == "move_log":
                        print("Received move log update")
                        self.move_log = data["moves"]
                        self._calculate_move_log_content_height()  # Calculate height after updating moves
                        # Scroll to bottom when new moves are added
                        max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
                        self.move_log_scroll = max_scroll
                    elif message_type == "rack_update":
                        print("Received rack update")
                        self.tile_rack = data.get('rack', [])
                        self.tiles_remaining = data.get('tiles_remaining', 0)
                        print(f"Rack updated: {self.tile_rack} (Tiles remaining: {self.tiles_remaining})")
                        # Clear buffer after successful move
                        self.letter_buffer.clear()
                        if hasattr(self, '_pending_buffer'):
                            del self._pending_buffer
                        if hasattr(self, '_pending_rack'):
                            del self._pending_rack
                    elif message_type == "tiles_remaining":
                        print("Received tiles remaining update")
                        self.tiles_remaining = data.get('tiles_remaining', 0)
                        self.tile_distribution = data.get('distribution', {})
                        print(f"Tiles remaining updated: {self.tiles_remaining}")
                        print(f"Tile distribution: {self.tile_distribution}")
                    elif message_type == "game_start":
                        print("Game started!")
                        self.game_started = True
                        self.ready = True
                        # Request rack update when game starts
                        try:
                            self.sock.sendall(b"GET_RACK\n")
                        except Exception as e:
                            print(f"Failed to request rack update: {e}")
                    elif message_type == "board_update":
                        print("Received board update with blanks")
                        # Return any buffered tiles to the rack before updating board
                        if self.letter_buffer:
                            print("[DEBUG] Returning buffered tiles to rack due to board update")
                            self._return_all_letters()
                        # Store the blank positions before any operations
                        blank_positions = set(tuple(pos) for pos in data['blanks'])
                        # Update the board and blank tiles before any buffer operations
                        self.board = data['board']
                        self.blank_tiles = blank_positions
                        # Only clear confirmed positions from buffer
                        self._clear_confirmed_buffer_positions()
                        # Clear buffer after successful move
                        self.letter_buffer.clear()
                        if hasattr(self, '_pending_buffer'):
                            del self._pending_buffer
                        if hasattr(self, '_pending_rack'):
                            del self._pending_rack
                    else:
                        print(f"Unknown message type: {data}")
            except json.JSONDecodeError:
                if message.startswith("ERROR:") or message.startswith("Error:") or message.startswith("Exchange Error:"):
                    err_msg = message.split(":", 1)[1].strip() if ":" in message else message
                    print(f"Server error: {err_msg}")
                    self._set_error(err_msg)
                    # Restore buffer and rack if a move was pending
                    if hasattr(self, '_pending_buffer') and hasattr(self, '_pending_rack'):
                        self.letter_buffer = self._pending_buffer.copy()
                        self.tile_rack = self._pending_rack.copy()
                        del self._pending_buffer
                        del self._pending_rack
                    if "shutting down" in message.lower():
                        print("Server is shutting down, returning to connection screen...")
                        self._handle_server_disconnect("Server is shutting down")
                        return
                elif message.startswith("OK:"):
                    print(f"Server confirmation: {message[3:]}")
                else:
                    print(f"Unknown message format: {message}")
        except Exception as e:
            print(f"Error processing server message: {e}")
            print(f"Raw message was: {repr(message)}")

    def _clear_confirmed_buffer_positions(self):
        """Remove buffer entries that are now confirmed on the server."""
        positions_to_remove = []
        for (row, col) in self.letter_buffer:
            if self.board[row][col] != '':
                positions_to_remove.append((row, col))
        
        for pos in positions_to_remove:
            del self.letter_buffer[pos]

    def draw_board(self):
        """Draw the game board, tile rack, info panel, and buttons."""
        with self.state_lock:
            # Clear the screen first
            self.screen.fill((255, 255, 255))
            
            if self.game_ended:
                self._draw_game_end_screen()
            else:
                self._draw_board_tiles()
                self._draw_tile_rack()
                self._draw_info_panel()
                self._draw_error_box()
                self._draw_buttons()
                self.draw_player_list()
                self.draw_move_log()
                
                # Draw blank tile dialog last, so it appears on top of everything
                if self.showing_blank_dialog:
                    self._draw_blank_dialog()
                # Draw unseen tiles dialog if active
                if self.showing_unseen_tiles:
                    self._draw_unseen_tiles_dialog()
            
            # Force update the display
            pygame.display.flip()

    def _draw_game_end_screen(self):
        # Draw semi-transparent overlay first
        overlay = pygame.Surface((self.WIDTH, self.HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 128))
        self.screen.blit(overlay, (0, 0))
        
        # Calculate base height and additional height needed
        base_height = 80  # Base height for title and basic content
        winner_height = 0
        if self.winner:
            max_score = max(self.final_scores.values())
            winners = [k for k, v in self.final_scores.items() if v == max_score]
            if len(winners) > 1:
                # Height for draw message, winners list, and spacing
                winner_height = 40 + (len(winners) * 20) + 20
            else:
                # Height for single winner message
                winner_height = 20
        
        # Height for final scores (all players)
        scores_height = len(self.final_scores) * 20
        
        # Calculate total height needed
        box_height = base_height + winner_height + scores_height + 100  # Increased height for button
        
        # Draw game end box
        box_width = 400
        box_x = (self.WIDTH - box_width) // 2
        box_y = (self.HEIGHT - box_height) // 2
        
        # Draw white background for the box
        pygame.draw.rect(self.screen, (255, 255, 255), 
                        (box_x, box_y, box_width, box_height))
        pygame.draw.rect(self.screen, (0, 0, 0), 
                        (box_x, box_y, box_width, box_height), 2)
        
        # Create fixed-size fonts for the dialog
        title_font = pygame.font.SysFont(None, 36)  # Fixed size for title
        main_font = pygame.font.SysFont(None, 24)   # Fixed size for main text
        info_font = pygame.font.SysFont(None, 18)   # Fixed size for info text
        button_font = pygame.font.SysFont(None, 20) # Fixed size for button text
        
        # Draw title
        title = title_font.render("Game Over!", True, (0, 0, 0))
        title_rect = title.get_rect(centerx=box_x + box_width//2, 
                                  y=box_y + 20)
        self.screen.blit(title, title_rect)
        
        # Draw winner or draw message
        if self.winner:
            # Check if there are multiple winners (draw)
            max_score = max(self.final_scores.values())
            winners = [k for k, v in self.final_scores.items() if v == max_score]
            
            if len(winners) > 1:
                # It's a draw
                draw_text = "It's a Draw!"
                draw_surface = main_font.render(draw_text, True, (0, 0, 200))  # Blue color for draw
                draw_rect = draw_surface.get_rect(centerx=box_x + box_width//2,
                                                y=box_y + 60)
                self.screen.blit(draw_surface, draw_rect)
                
                # Draw "Winners:" text
                winners_text = "Winners:"
                winners_surface = main_font.render(winners_text, True, (0, 0, 0))
                winners_rect = winners_surface.get_rect(centerx=box_x + box_width//2,
                                                      y=box_y + 80)
                self.screen.blit(winners_surface, winners_rect)
                
                # Draw each winner's name
                y_offset = box_y + 100
                for winner in winners:
                    winner_text = f"{winner}"
                    winner_surface = main_font.render(winner_text, True, (0, 200, 0))  # Green for winners
                    winner_rect = winner_surface.get_rect(centerx=box_x + box_width//2,
                                                        y=y_offset)
                    self.screen.blit(winner_surface, winner_rect)
                    y_offset += 20
            else:
                # Single winner
                winner_text = f"Winner: {self.winner}"
                winner_surface = main_font.render(winner_text, True, (0, 200, 0))
                winner_rect = winner_surface.get_rect(centerx=box_x + box_width//2,
                                                    y=box_y + 60)
                self.screen.blit(winner_surface, winner_rect)
        
        # Draw final scores
        y_offset = box_y + 100 if len(winners) <= 1 else box_y + 100 + (len(winners) * 20) + 20
        for username, score in sorted(self.final_scores.items(), key=lambda x: x[1], reverse=True):
            score_text = f"{username}: {score} points"
            score_surface = main_font.render(score_text, True, (0, 0, 0))
            score_rect = score_surface.get_rect(centerx=box_x + box_width//2,
                                              y=y_offset)
            self.screen.blit(score_surface, score_rect)
            y_offset += 20
        
        # Draw Return to Connection button
        button_width = 200
        button_height = 40
        button_x = box_x + (box_width - button_width) // 2
        button_y = box_y + box_height - 80
        
        self.return_to_connection_button = pygame.Rect(button_x, button_y, button_width, button_height)
        pygame.draw.rect(self.screen, (100, 200, 255), self.return_to_connection_button)  # Light blue color
        pygame.draw.rect(self.screen, (0, 0, 0), self.return_to_connection_button, 2)
        
        button_text = "Return to Connection"
        text_surface = button_font.render(button_text, True, (0, 0, 0))
        text_rect = text_surface.get_rect(center=self.return_to_connection_button.center)
        self.screen.blit(text_surface, text_rect)
        
        # Draw instructions
        instructions = info_font.render("Press Q to quit", True, (100, 100, 100))
        instructions_rect = instructions.get_rect(centerx=box_x + box_width//2,
                                                y=box_y + box_height - 20)
        self.screen.blit(instructions, instructions_rect)

    def _draw_board_tiles(self):
        """Draw the game board, tile rack, info panel, and buttons."""
        for r in range(self.BOARD_SIZE):
            for c in range(self.BOARD_SIZE):
                x = self.MARGIN + c * self.TILE_SIZE
                y = self.MARGIN + r * self.TILE_SIZE
                rect = pygame.Rect(x, y, self.TILE_SIZE, self.TILE_SIZE)

                # Determine what to display
                server_letter = self.board[r][c]
                buffer_letter = self.letter_buffer.get((r, c))
                
                if server_letter:
                    # Server-confirmed letter - draw white tile with letter
                    color = self.LETTER_COLORS['placed']
                    pygame.draw.rect(self.screen, color, rect)
                    pygame.draw.rect(self.screen, (0, 0, 0), rect, 2)
                    
                    # Use purple text for blank tiles
                    text_color = self.LETTER_TEXT_COLORS['blank'] if (r, c) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
                    text = self.font.render(server_letter, True, text_color)
                    text_rect = text.get_rect(center=rect.center)
                    self.screen.blit(text, text_rect)
                    
                    # Draw score number (bottom right)
                    # Always show 0 for blank tiles
                    score = self.LETTER_VALUES.get('?') if (r, c) in self.blank_tiles else self.LETTER_VALUES.get(server_letter.upper(), 0)
                    score_text = self.score_font.render(str(score), True, (80, 80, 80))
                    score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, y + self.TILE_SIZE - 2))
                    self.screen.blit(score_text, score_rect)
                    
                elif buffer_letter:
                    # Client buffer letter - draw yellow tile with letter
                    color = self.LETTER_COLORS['buffered']
                    pygame.draw.rect(self.screen, color, rect)
                    pygame.draw.rect(self.screen, (0, 0, 0), rect, 2)
                    
                    # Use purple text for blank tiles
                    text_color = self.LETTER_TEXT_COLORS['blank'] if (r, c) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
                    text = self.font.render(buffer_letter, True, text_color)
                    text_rect = text.get_rect(center=rect.center)
                    self.screen.blit(text, text_rect)
                    
                    # Draw score number (bottom right)
                    # Always show 0 for blank tiles
                    score = self.LETTER_VALUES.get('?') if (r, c) in self.blank_tiles else self.LETTER_VALUES.get(buffer_letter.upper(), 0)
                    score_text = self.score_font.render(str(score), True, (80, 80, 80))
                    score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, y + self.TILE_SIZE - 2))
                    self.screen.blit(score_text, score_rect)
                    
                else:
                    # Empty tile - show special tile background and text
                    special = self.special_tiles[r][c]
                    color = self.SPECIAL_COLORS.get(special, (240, 217, 181))
                    
                    pygame.draw.rect(self.screen, color, rect)
                    pygame.draw.rect(self.screen, (0, 0, 0), rect, 1)

                    # Draw special tile text (e.g. TW, DL)
                    if special:
                        text = self.font.render(special, True, (0, 0, 0))
                        text_rect = text.get_rect(center=(x + self.TILE_SIZE // 2, y + self.TILE_SIZE // 2))
                        self.screen.blit(text, text_rect)

                # Highlight selected board cell
                if self.selected_board_cell == (r, c):
                    pygame.draw.rect(self.screen, (255, 0, 0), rect, 3)

        # Draw ghost tile for valid drop position
        if self.dragging_tile:
            mouse_x, mouse_y = pygame.mouse.get_pos()
            # Calculate tile center position
            tile_center_x = mouse_x - self.drag_offset[0]
            tile_center_y = mouse_y - self.drag_offset[1]
            col = (tile_center_x - self.MARGIN) // self.TILE_SIZE
            row = (tile_center_y - self.MARGIN) // self.TILE_SIZE
            
            if 0 <= row < self.BOARD_SIZE and 0 <= col < self.BOARD_SIZE:
                if self.board[row][col] == '' and (row, col) not in self.letter_buffer:
                    ghost_rect = pygame.Rect(
                        self.MARGIN + col * self.TILE_SIZE,
                        self.MARGIN + row * self.TILE_SIZE,
                        self.TILE_SIZE,
                        self.TILE_SIZE
                    )
                    # Draw semi-transparent ghost tile
                    ghost_surface = pygame.Surface((self.TILE_SIZE, self.TILE_SIZE), pygame.SRCALPHA)
                    ghost_surface.fill((200, 200, 200, 180))  # Semi-transparent gray
                    pygame.draw.rect(ghost_surface, (0, 0, 0), ghost_surface.get_rect(), 2)
                    
                    # Draw ghost letter
                    if self.dragging_from_board:
                        row, col = self.drag_board_pos
                        letter = self.letter_buffer[(row, col)]
                        text_color = self.LETTER_TEXT_COLORS['blank'] if (row, col) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
                    else:
                        letter = self.tile_rack[self.drag_current_index]
                        text_color = self.LETTER_TEXT_COLORS['blank'] if letter == '?' else self.LETTER_TEXT_COLORS['normal']
                    
                    text = self.font.render(letter, True, text_color)
                    text_rect = text.get_rect(center=(self.TILE_SIZE // 2, self.TILE_SIZE // 2))
                    ghost_surface.blit(text, text_rect)
                    
                    # Draw ghost score number
                    if self.dragging_from_board:
                        row, col = self.drag_board_pos
                        score = self.LETTER_VALUES.get('?') if (row, col) in self.blank_tiles else self.LETTER_VALUES.get(letter.upper(), 0)
                    else:
                        score = self.LETTER_VALUES.get('?') if letter == '?' else self.LETTER_VALUES.get(letter.upper(), 0)
                    
                    score_font = pygame.font.SysFont(None, 16)
                    score_text = score_font.render(str(score), True, (80, 80, 80))
                    score_rect = score_text.get_rect(bottomright=(self.TILE_SIZE - 3, self.TILE_SIZE - 2))
                    ghost_surface.blit(score_text, score_rect)
                    
                    self.screen.blit(ghost_surface, ghost_rect)

        # Draw the tile being dragged
        if self.dragging_tile:
            mouse_x, mouse_y = pygame.mouse.get_pos()
            x = mouse_x - self.drag_offset[0] - self.TILE_SIZE // 2
            y = mouse_y - self.drag_offset[1] - self.TILE_SIZE // 2
            rect = pygame.Rect(x, y, self.TILE_SIZE, self.TILE_SIZE)
            
            # Draw dragged tile
            pygame.draw.rect(self.screen, self.LETTER_COLORS['dragging'], rect)
            pygame.draw.rect(self.screen, (0, 0, 0), rect, 2)
            
            # Draw letter
            if self.dragging_from_board:
                row, col = self.drag_board_pos
                letter = self.letter_buffer[(row, col)]
                text_color = self.LETTER_TEXT_COLORS['blank'] if (row, col) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
            else:
                letter = self.tile_rack[self.drag_current_index]
                text_color = self.LETTER_TEXT_COLORS['blank'] if letter == '?' else self.LETTER_TEXT_COLORS['normal']
            
            text = self.font.render(letter, True, text_color)
            text_rect = text.get_rect(center=rect.center)
            self.screen.blit(text, text_rect)
            
            # Draw score number
            if self.dragging_from_board:
                row, col = self.drag_board_pos
                score = self.LETTER_VALUES.get('?') if (row, col) in self.blank_tiles else self.LETTER_VALUES.get(letter.upper(), 0)
            else:
                score = self.LETTER_VALUES.get('?') if letter == '?' else self.LETTER_VALUES.get(letter.upper(), 0)
            
            score_font = pygame.font.SysFont(None, 16)
            score_text = score_font.render(str(score), True, (80, 80, 80))
            score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, y + self.TILE_SIZE - 2))
            self.screen.blit(score_text, score_rect)

        # Draw word previews if there are buffered letters
        if self.letter_buffer:
            words = self._get_all_words(self.letter_buffer)
            for word, positions, is_horizontal in words:
                # Calculate word rectangle
                min_row = min(r for r, _ in positions)
                max_row = max(r for r, _ in positions)
                min_col = min(c for _, c in positions)
                max_col = max(c for _, c in positions)
                
                # Draw rectangle around word
                rect_x = self.MARGIN + min_col * self.TILE_SIZE
                rect_y = self.MARGIN + min_row * self.TILE_SIZE
                rect_width = (max_col - min_col + 1) * self.TILE_SIZE
                rect_height = (max_row - min_row + 1) * self.TILE_SIZE
                
                # Check if word is valid
                is_valid = self._is_valid_word(word)
                color = (0, 180, 0) if is_valid else (255, 0, 0)
                
                # Draw rectangle
                pygame.draw.rect(self.screen, color, (rect_x, rect_y, rect_width, rect_height), 2)
                
                # Calculate and draw score
                score = self._calculate_word_score(word, positions)
                score_text = self.font.render(str(score), True, color)
                
                # Determine score position based on word orientation and position
                if is_horizontal:
                    # For horizontal words
                    if min_col == 0:  # Word starts at left edge
                        score_x = rect_x + rect_width + 2
                    else:
                        score_x = rect_x - score_text.get_width() - 2
                    score_y = rect_y + 2
                else:
                    # For vertical words
                    score_x = rect_x + 2
                    if min_row == 0:  # Word starts at top edge
                        score_y = rect_y + rect_height + 2
                    else:
                        score_y = rect_y - 17
                
                self.screen.blit(score_text, (score_x, score_y))

        # Draw last move rectangles and scores
        if self.move_log and not self.letter_buffer:
            last_move = self.move_log[-1]
            if 'words' in last_move:  # Only for regular moves, not passes or exchanges
                for word_info in last_move['words']:
                    positions = [(r, c) for r, c, _, _ in word_info['positions']]
                    if positions:
                        # Calculate word rectangle
                        min_row = min(r for r, _ in positions)
                        max_row = max(r for r, _ in positions)
                        min_col = min(c for _, c in positions)
                        max_col = max(c for _, c in positions)
                        
                        # Draw purple rectangle around word
                        rect_x = self.MARGIN + min_col * self.TILE_SIZE
                        rect_y = self.MARGIN + min_row * self.TILE_SIZE
                        rect_width = (max_col - min_col + 1) * self.TILE_SIZE
                        rect_height = (max_row - min_row + 1) * self.TILE_SIZE
                        
                        # Draw rectangle in purple
                        pygame.draw.rect(self.screen, (128, 0, 128), (rect_x, rect_y, rect_width, rect_height), 2)
                        
                        # Use the actual score from the move log instead of recalculating
                        score = word_info.get('score', 0)  # Get score from move log
                        score_text = self.font.render(str(score), True, (128, 0, 128))
                        
                        # Determine score position based on word orientation and position
                        is_horizontal = min_row == max_row
                        if is_horizontal:
                            # For horizontal words
                            if min_col == 0:  # Word starts at left edge
                                score_x = rect_x + rect_width + 2
                            else:
                                score_x = rect_x - score_text.get_width() - 2
                            score_y = rect_y + 2
                        else:
                            # For vertical words
                            score_x = rect_x + 2
                            if min_row == 0:  # Word starts at top edge
                                score_y = rect_y + rect_height + 2
                            else:
                                score_y = rect_y - 17
                        
                        self.screen.blit(score_text, (score_x, score_y))

    def _draw_tile_rack(self):
        """Draw the player's tile rack."""
        rack_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 10
        
        # Calculate rack width based on whether we're dragging from board or rack
        if self.dragging_tile:
            if self.dragging_from_board:
                # When dragging from board, add space for ghost tile
                rack_width = len(self.tile_rack) * (self.TILE_SIZE + 5) + 5
                is_dragging_to_rack = False
                drop_index = None
                mouse_x, mouse_y = pygame.mouse.get_pos()
                if rack_y <= mouse_y <= rack_y + self.TILE_SIZE:
                    rack_x = self.MARGIN + len(self.tile_rack) * (self.TILE_SIZE + 5)
                    if mouse_x >= self.MARGIN and mouse_x <= rack_x + self.TILE_SIZE + 5:
                        # Calculate drop index based on tile center position
                        tile_center_x = mouse_x - self.drag_offset[0]
                        drop_index = (tile_center_x - self.MARGIN) // (self.TILE_SIZE + 5)
                        drop_index = max(0, min(drop_index, len(self.tile_rack)))
                        rack_width += self.TILE_SIZE + 5  # Add space for ghost tile
                        is_dragging_to_rack = True
            else:
                # When dragging from rack, check if we're hovering over the rack
                mouse_x, mouse_y = pygame.mouse.get_pos()
                if rack_y <= mouse_y <= rack_y + self.TILE_SIZE:
                    # When hovering over rack, keep full width but don't show ghost
                    rack_width = len(self.tile_rack) * (self.TILE_SIZE + 5) + 5
                    is_dragging_to_rack = True
                    drop_index = (mouse_x - self.MARGIN) // (self.TILE_SIZE + 5)
                    drop_index = max(0, min(drop_index, len(self.tile_rack)))
                else:
                    # When not hovering over rack, remove the dragged tile's space
                    rack_width = (len(self.tile_rack) - 1) * (self.TILE_SIZE + 5) + 5
                    is_dragging_to_rack = False
                    drop_index = None
        else:
            rack_width = len(self.tile_rack) * (self.TILE_SIZE + 5) + 5
            is_dragging_to_rack = False
            drop_index = None
        
        # Draw rack background
        rack_bg = pygame.Rect(self.MARGIN - 5, rack_y - 5, rack_width, self.TILE_SIZE + 10)
        pygame.draw.rect(self.screen, (220, 220, 220), rack_bg)
        pygame.draw.rect(self.screen, (100, 100, 100), rack_bg, 2)
        
        # Draw tiles
        for i, letter in enumerate(self.tile_rack):
            # Skip drawing the tile being dragged
            if self.dragging_tile and i == self.drag_current_index:
                continue
                
            # Calculate x position, adjusting for the dragged tile's position
            if is_dragging_to_rack and i >= drop_index and self.dragging_from_board:
                x = self.MARGIN + (i + 1) * (self.TILE_SIZE + 5)  # Shift tiles right of drop position
            else:
                # When dragging from rack and not hovering over rack, adjust positions to fill the gap
                if self.dragging_tile and not self.dragging_from_board and not is_dragging_to_rack and i > self.drag_current_index:
                    x = self.MARGIN + (i - 1) * (self.TILE_SIZE + 5)
                else:
                    x = self.MARGIN + i * (self.TILE_SIZE + 5)
            
            rect = pygame.Rect(x, rack_y, self.TILE_SIZE, self.TILE_SIZE)
            
            # Highlight selected tile
            if self.exchange_mode:
                color = (255, 200, 200) if i in self.tiles_to_exchange else self.LETTER_COLORS['rack']
            else:
                color = self.LETTER_COLORS['rack_selected'] if i == self.selected_rack_index else self.LETTER_COLORS['rack']
            
            pygame.draw.rect(self.screen, color, rect)
            pygame.draw.rect(self.screen, (0, 0, 0), rect, 2)

            # Draw letter
            text_color = self.LETTER_TEXT_COLORS['blank'] if letter == '?' else self.LETTER_TEXT_COLORS['normal']
            text = self.font.render(letter, True, text_color)
            text_rect = text.get_rect(center=rect.center)
            self.screen.blit(text, text_rect)

            # Draw score number (bottom right)
            # Always show 0 for blank tiles
            score = self.LETTER_VALUES.get('?') if letter == '?' else self.LETTER_VALUES.get(letter.upper(), 0)
            score_text = self.score_font.render(str(score), True, (80, 80, 80))
            score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, rack_y + self.TILE_SIZE - 2))
            self.screen.blit(score_text, score_rect)
        
        # Draw the tile being dragged
        if self.dragging_tile:
            mouse_x, mouse_y = pygame.mouse.get_pos()
            x = mouse_x - self.drag_offset[0] - self.TILE_SIZE // 2
            y = mouse_y - self.drag_offset[1] - self.TILE_SIZE // 2
            rect = pygame.Rect(x, y, self.TILE_SIZE, self.TILE_SIZE)
            
            # Draw dragged tile
            pygame.draw.rect(self.screen, self.LETTER_COLORS['dragging'], rect)
            pygame.draw.rect(self.screen, (0, 0, 0), rect, 2)
            
            # Draw letter
            if self.dragging_from_board:
                row, col = self.drag_board_pos
                letter = self.letter_buffer[(row, col)]
                text_color = self.LETTER_TEXT_COLORS['blank'] if (row, col) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
            else:
                letter = self.tile_rack[self.drag_current_index]
                text_color = self.LETTER_TEXT_COLORS['blank'] if letter == '?' else self.LETTER_TEXT_COLORS['normal']
            
            text = self.font.render(letter, True, text_color)
            text_rect = text.get_rect(center=rect.center)
            self.screen.blit(text, text_rect)
            
            # Draw score number
            if self.dragging_from_board:
                row, col = self.drag_board_pos
                score = self.LETTER_VALUES.get('?') if (row, col) in self.blank_tiles else self.LETTER_VALUES.get(letter.upper(), 0)
            else:
                score = self.LETTER_VALUES.get('?') if letter == '?' else self.LETTER_VALUES.get(letter.upper(), 0)
            
            score_font = pygame.font.SysFont(None, 16)
            score_text = score_font.render(str(score), True, (80, 80, 80))
            score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, y + self.TILE_SIZE - 2))
            self.screen.blit(score_text, score_rect)

    def _draw_info_panel(self):
        """Draw the information panel showing tiles remaining and rack count."""
        info_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + self.RACK_HEIGHT + 5
        
        # Calculate width to end before move log with margin
        move_log_x = self.WIDTH - self.PLAYER_LIST_WIDTH - 20  # X position of move log
        info_width = move_log_x - self.MARGIN - 20  # Width from left margin to move log minus margin
        
        # Background for info panel
        info_bg = pygame.Rect(self.MARGIN, info_y, info_width, self.INFO_HEIGHT - 10)
        pygame.draw.rect(self.screen, (240, 240, 240), info_bg)
        pygame.draw.rect(self.screen, (150, 150, 150), info_bg, 1)
        
        # Calculate column positions
        first_col_x = self.MARGIN + 10
        second_col_x = self.MARGIN + info_width // 2
        
        # First column: Tiles remaining and rack count
        tiles_text = f"Tiles in bag: {self.tiles_remaining}"
        tiles_surface = self.info_font.render(tiles_text, True, (0, 0, 0))
        self.screen.blit(tiles_surface, (first_col_x, info_y + 5))
        
        rack_text = f"Your tiles: {len(self.tile_rack)}/7"
        rack_surface = self.info_font.render(rack_text, True, (0, 0, 0))
        self.screen.blit(rack_surface, (first_col_x, info_y + 25))
        
        # Second column: Buffer info and turn status
        if self.letter_buffer:
            buffer_text = f"Placed letters: {len(self.letter_buffer)}"
            buffer_surface = self.info_font.render(buffer_text, True, (0, 0, 0))
            self.screen.blit(buffer_surface, (second_col_x, info_y + 5))
        
        # Show waiting message if not started
        if not self.game_started:
            wait_text = "Waiting for all players to be ready..."
            wait_surface = self.info_font.render(wait_text, True, (200, 0, 0))
            self.screen.blit(wait_surface, (second_col_x, info_y + 25))
        # Show "Your turn" message if it's the current player's turn
        elif self.game_started and not self.game_ended:
            # Find the current player's username
            current_player = next((player for player in self.players if player.get("current_turn", False)), None)
            if current_player and current_player.get("username") == self.username:
                turn_text = "Your turn"
                turn_surface = self.info_font.render(turn_text, True, (0, 200, 0))  # Green color
                self.screen.blit(turn_surface, (second_col_x, info_y + 25))

    def _draw_error_box(self):
        """Draw a separate error box below the info panel if there is an error message."""
        if not self.error_message:
            return
        # Box dimensions
        move_log_x = self.WIDTH - self.PLAYER_LIST_WIDTH - 20  # X position of move log
        box_width = move_log_x - self.MARGIN - 20  # Width from left margin to move log minus margin
        box_height = 36
        box_x = self.MARGIN
        spacing_above_error = 15  # space between info panel and error box
        # Place the box just below the info panel, above the rack and buttons
        info_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + self.RACK_HEIGHT + self.INFO_HEIGHT
        box_y = info_y + spacing_above_error
        # Draw box background and border
        pygame.draw.rect(self.screen, (255, 240, 240), (box_x, box_y, box_width, box_height))
        pygame.draw.rect(self.screen, (200, 0, 0), (box_x, box_y, box_width, box_height), 2)
        # Draw error text
        err_surface = self.info_font.render(self.error_message, True, (200, 0, 0))
        err_rect = err_surface.get_rect(center=(box_x + box_width // 2, box_y + box_height // 2))
        self.screen.blit(err_surface, err_rect)

    def _draw_buttons(self):
        """Draw the control buttons."""
        # Return button
        pygame.draw.rect(self.screen, (200, 200, 200), self.return_button)
        pygame.draw.rect(self.screen, (0, 0, 0), self.return_button, 2)
        # Split text to make first letter bold and underlined
        return_text = "Return"
        first_letter = self.button_font.render(return_text[0], True, (0, 0, 0))
        rest_text = self.button_font.render(return_text[1:], True, (0, 0, 0))
        # Draw first letter with underline
        first_rect = first_letter.get_rect(midleft=self.return_button.midleft)
        first_rect.x += 10  # Add some padding
        self.screen.blit(first_letter, first_rect)
        pygame.draw.line(self.screen, (0, 0, 0), 
                        (first_rect.left, first_rect.bottom),
                        (first_rect.right, first_rect.bottom), 2)
        # Draw rest of text
        rest_rect = rest_text.get_rect(midleft=first_rect.midright)
        self.screen.blit(rest_text, rest_rect)
        
        # Send button
        if self.exchange_mode:
            button_color = (100, 200, 100) if self.tiles_to_exchange else (150, 150, 150)
        else:
            button_color = (100, 200, 100) if self.letter_buffer and self.game_started else (150, 150, 150)
        pygame.draw.rect(self.screen, button_color, self.send_button)
        pygame.draw.rect(self.screen, (0, 0, 0), self.send_button, 2)
        # Split text to make first letter bold and underlined
        send_text = "Done"
        first_letter = self.button_font.render(send_text[0], True, (0, 0, 0))
        rest_text = self.button_font.render(send_text[1:], True, (0, 0, 0))
        # Draw first letter with underline
        first_rect = first_letter.get_rect(midleft=self.send_button.midleft)
        first_rect.x += 10  # Add some padding
        self.screen.blit(first_letter, first_rect)
        pygame.draw.line(self.screen, (0, 0, 0), 
                        (first_rect.left, first_rect.bottom),
                        (first_rect.right, first_rect.bottom), 2)
        # Draw rest of text
        rest_rect = rest_text.get_rect(midleft=first_rect.midright)
        self.screen.blit(rest_text, rest_rect)
        
        # Exchange button - always visible but grayed out if game not started
        if self.game_started:
            exchange_color = (255, 200, 200) if self.exchange_mode else (180, 180, 180)
        else:
            exchange_color = (150, 150, 150)  # Grayed out when game not started
        pygame.draw.rect(self.screen, exchange_color, self.exchange_button)
        pygame.draw.rect(self.screen, (0, 0, 0), self.exchange_button, 2)
        # Split text to make first letter bold and underlined
        exchange_text = "Exchange"
        first_letter = self.button_font.render(exchange_text[0], True, (0, 0, 0))
        rest_text = self.button_font.render(exchange_text[1:], True, (0, 0, 0))
        # Draw first letter with underline
        first_rect = first_letter.get_rect(midleft=self.exchange_button.midleft)
        first_rect.x += 10  # Add some padding
        self.screen.blit(first_letter, first_rect)
        pygame.draw.line(self.screen, (0, 0, 0), 
                        (first_rect.left, first_rect.bottom),
                        (first_rect.right, first_rect.bottom), 2)
        # Draw rest of text
        rest_rect = rest_text.get_rect(midleft=first_rect.midright)
        self.screen.blit(rest_text, rest_rect)
        
        # Ready button (only if game not started)
        if not self.game_started:
            ready_color = (100, 200, 255) if not self.ready else (0, 200, 0)  # Green when ready
            pygame.draw.rect(self.screen, ready_color, self.ready_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.ready_button, 2)
            # Split text to make first letter bold and underlined
            ready_text = "Ready"
            first_letter = self.button_font.render(ready_text[0], True, (0, 0, 0))
            rest_text = self.button_font.render(ready_text[1:], True, (0, 0, 0))
            # Draw first letter with underline
            first_rect = first_letter.get_rect(midleft=self.ready_button.midleft)
            first_rect.x += 10  # Add some padding
            self.screen.blit(first_letter, first_rect)
            pygame.draw.line(self.screen, (0, 0, 0), 
                            (first_rect.left, first_rect.bottom),
                            (first_rect.right, first_rect.bottom), 2)
            # Draw rest of text
            rest_rect = rest_text.get_rect(midleft=first_rect.midright)
            self.screen.blit(rest_text, rest_rect)
        
        # Pass button (only if game started and player is ready)
        if self.game_started and self.ready and not self.game_ended:
            pass_color = (200, 200, 255)
            pygame.draw.rect(self.screen, pass_color, self.pass_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.pass_button, 2)
            # Split text to make first letter bold and underlined
            pass_text = "Pass"
            first_letter = self.button_font.render(pass_text[0], True, (0, 0, 0))
            rest_text = self.button_font.render(pass_text[1:], True, (0, 0, 0))
            # Draw first letter with underline
            first_rect = first_letter.get_rect(midleft=self.pass_button.midleft)
            first_rect.x += 10  # Add some padding
            self.screen.blit(first_letter, first_rect)
            pygame.draw.line(self.screen, (0, 0, 0), 
                            (first_rect.left, first_rect.bottom),
                            (first_rect.right, first_rect.bottom), 2)
            # Draw rest of text
            rest_rect = rest_text.get_rect(midleft=first_rect.midright)
            self.screen.blit(rest_text, rest_rect)
            
        # Shuffle button (only if game started and player is ready)
        if self.game_started and self.ready and not self.game_ended:
            shuffle_color = (200, 255, 200)  # Light green
            pygame.draw.rect(self.screen, shuffle_color, self.shuffle_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.shuffle_button, 2)
            # Split text to make first letter bold and underlined
            shuffle_text = "Shuffle"
            first_letter = self.button_font.render(shuffle_text[0], True, (0, 0, 0))
            rest_text = self.button_font.render(shuffle_text[1:], True, (0, 0, 0))
            # Draw first letter with underline
            first_rect = first_letter.get_rect(midleft=self.shuffle_button.midleft)
            first_rect.x += 10  # Add some padding
            self.screen.blit(first_letter, first_rect)
            pygame.draw.line(self.screen, (0, 0, 0), 
                            (first_rect.left, first_rect.bottom),
                            (first_rect.right, first_rect.bottom), 2)
            # Draw rest of text
            rest_rect = rest_text.get_rect(midleft=first_rect.midright)
            self.screen.blit(rest_text, rest_rect)

        # Unseen tiles button (only if game started and player is ready)
        if self.game_started and self.ready and not self.game_ended:
            unseen_color = (255, 200, 255)  # Light purple
            pygame.draw.rect(self.screen, unseen_color, self.unseen_tiles_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.unseen_tiles_button, 2)
            # Split text to make first letter bold and underlined
            unseen_text = "Unseen"
            first_letter = self.button_font.render(unseen_text[0], True, (0, 0, 0))
            rest_text = self.button_font.render(unseen_text[1:], True, (0, 0, 0))
            # Draw first letter with underline
            first_rect = first_letter.get_rect(midleft=self.unseen_tiles_button.midleft)
            first_rect.x += 10  # Add some padding
            self.screen.blit(first_letter, first_rect)
            pygame.draw.line(self.screen, (0, 0, 0), 
                            (first_rect.left, first_rect.bottom),
                            (first_rect.right, first_rect.bottom), 2)
            # Draw rest of text
            rest_rect = rest_text.get_rect(midleft=first_rect.midright)
            self.screen.blit(rest_text, rest_rect)

    def draw_player_list(self):
        """Draw player list in the UI."""
        # Position in top right corner, with more centered margins
        player_x = self.WIDTH - self.PLAYER_LIST_WIDTH - 20  # Increased left margin
        player_y = self.MARGIN
        
        # Draw background
        pygame.draw.rect(self.screen, (240, 240, 240), 
                        (player_x, player_y, self.PLAYER_LIST_WIDTH, 150))
        pygame.draw.rect(self.screen, (150, 150, 150), 
                        (player_x, player_y, self.PLAYER_LIST_WIDTH, 150), 1)
        
        # Draw title
        title_font = pygame.font.SysFont(None, 20)
        title = title_font.render("Players", True, (0, 0, 0))
        title_rect = title.get_rect(centerx=player_x + self.PLAYER_LIST_WIDTH // 2, y=player_y + 5)
        self.screen.blit(title, title_rect)
        
        # Draw player list
        for i, player in enumerate(self.players):
            if not self.game_started:
                # Before game start, show ready status
                status = "Ready" if player["ready"] else "Not Ready"
                color = (0, 200, 0) if player["ready"] else (200, 0, 0)
                # Add "(you)" to current player's name
                username = f"{player['username']} (you)" if player['username'] == self.username else player['username']
                text = f"{username}: {status}"
            else:
                # After game start, show points and turn
                color = (0, 200, 0) if player["current_turn"] else (0, 0, 0)
                # Add "(you)" to current player's name
                username = f"{player['username']} (you)" if player['username'] == self.username else player['username']
                text = f"{username}: {player['points']} pts"
                
            player_surface = self.info_font.render(text, True, color)
            player_rect = player_surface.get_rect(x=player_x + 10, y=player_y + 30 + 20 * i)
            self.screen.blit(player_surface, player_rect)

    def _handle_rack_click(self, x, y):
        """Handle clicks on the tile rack."""
        rack_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 10
        
        if rack_y <= y <= rack_y + self.TILE_SIZE:
            for i in range(len(self.tile_rack)):
                rect = pygame.Rect(self.MARGIN + i * (self.TILE_SIZE + 5), rack_y, self.TILE_SIZE, self.TILE_SIZE)
                if rect.collidepoint(x, y):
                    if self.exchange_mode:
                        # Toggle tile selection for exchange
                        if i in self.tiles_to_exchange:
                            self.tiles_to_exchange.remove(i)
                        else:
                            self.tiles_to_exchange.add(i)
                    else:
                        # Initialize drag state
                        self.dragging_tile = True
                        self.drag_start_index = i
                        self.drag_current_index = i
                        self.drag_start_pos = (x, y)
                        # Calculate offset from mouse to tile center
                        tile_center_x = self.MARGIN + i * (self.TILE_SIZE + 5) + self.TILE_SIZE // 2
                        tile_center_y = rack_y + self.TILE_SIZE // 2
                        self.drag_offset = (x - tile_center_x, y - tile_center_y)
                    return True
        return False

    def _handle_board_click(self, x, y):
        """Handle clicks on the game board."""
        if not self.game_started:
            self._set_error("Game has not started yet. Wait for all players to be ready.")
            return
            
        col = (x - self.MARGIN) // self.TILE_SIZE
        row = (y - self.MARGIN) // self.TILE_SIZE
        
        if 0 <= row < self.BOARD_SIZE and 0 <= col < self.BOARD_SIZE:
            current_time = pygame.time.get_ticks()
            current_pos = (row, col)
            
            # Check for double click
            if (self.last_click_pos == current_pos and 
                current_time - self.last_click_time < self.DOUBLE_CLICK_TIME):
                # Double click detected - recall tile if it's in the buffer
                if (row, col) in self.letter_buffer:
                    letter = self.letter_buffer[(row, col)]
                    # If this was a blank tile, restore it as a blank
                    if (row, col) in self.blank_tiles:
                        self.tile_rack.append('?')
                        self.blank_tiles.remove((row, col))
                    else:
                        self.tile_rack.append(letter)
                    del self.letter_buffer[(row, col)]
                    self.selected_board_cell = None  # Deselect after moving
                self.last_click_time = 0  # Reset to prevent triple-click
                self.last_click_pos = None
                return
            
            # Update click tracking
            self.last_click_time = current_time
            self.last_click_pos = current_pos
            
            # Handle tile movement
            if self.selected_board_cell is not None:
                # If we have a selected tile in the buffer, move it
                old_row, old_col = self.selected_board_cell
                if (old_row, old_col) in self.letter_buffer:
                    # Check if new position is empty
                    if self.board[row][col] == '' and (row, col) not in self.letter_buffer:
                        # Move the tile
                        letter = self.letter_buffer[(old_row, old_col)]
                        del self.letter_buffer[(old_row, old_col)]
                        # If this was a blank tile, show the dialog again
                        if (old_row, old_col) in self.blank_tiles:
                            self.blank_tiles.remove((old_row, old_col))
                            self.blank_pos = (row, col)
                            self.showing_blank_dialog = True
                            self.selected_rack_index = None
                            self.selected_board_cell = None
                            return
                        else:
                            self.letter_buffer[(row, col)] = letter
                        self.selected_board_cell = None  # Deselect after moving
                        return
            
            # Normal tile selection
            self.selected_board_cell = (row, col)
            
            # If a tile from rack is selected, place it in buffer
            if self.selected_rack_index is not None:
                self._place_tile_in_buffer(row, col)
            # If we clicked on a buffered tile, start dragging it
            elif (row, col) in self.letter_buffer:
                self.dragging_tile = True
                self.dragging_from_board = True
                self.drag_board_pos = (row, col)
                self.drag_start_pos = (x, y)
                # Calculate offset from mouse to tile center
                tile_center_x = self.MARGIN + col * self.TILE_SIZE + self.TILE_SIZE // 2
                tile_center_y = self.MARGIN + row * self.TILE_SIZE + self.TILE_SIZE // 2
                self.drag_offset = (x - tile_center_x, y - tile_center_y)
                # Don't select the board cell when starting a drag
                self.selected_board_cell = None

    def _place_tile_in_buffer(self, row, col):
        """Place a selected tile from the rack into the client buffer."""
        if self.selected_rack_index is None:
            return
            
        # Check if selected index is valid
        if self.selected_rack_index >= len(self.tile_rack):
            self.selected_rack_index = None
            return
        
        # Check if position is already occupied (server or buffer)
        if self.board[row][col] != '' or (row, col) in self.letter_buffer:
            print(f"Position ({row}, {col}) is already occupied")
            return
            
        letter = self.tile_rack[self.selected_rack_index]
        
        # Handle blank tile
        if letter == '?':
            self.blank_pos = (row, col)
            self.showing_blank_dialog = True
            self.tile_rack.pop(self.selected_rack_index)  # Remove blank from rack immediately
            self.selected_rack_index = None  # Deselect after placing
            self.selected_board_cell = None  # Deselect board cell after placing
            return
        
        # Add to buffer and remove from rack
        self.letter_buffer[(row, col)] = letter
        self.tile_rack.pop(self.selected_rack_index)
        self.selected_rack_index = None  # Deselect after placing
        self.selected_board_cell = None  # Deselect board cell after placing

    def _return_all_letters(self):
        """Return all buffered letters back to the rack."""
        for (row, col), letter in self.letter_buffer.items():
            # If this was a blank tile, return it as '?' to the rack
            if (row, col) in self.blank_tiles:
                self.tile_rack.append('?')
                self.blank_tiles.remove((row, col))  # Remove only this specific blank position
            else:
                self.tile_rack.append(letter)
        
        self.letter_buffer.clear()
        # Don't clear all blank tiles, only remove the ones we just returned
        self.selected_rack_index = None
        self.selected_board_cell = None
        print("All letters returned to rack")

    def _send_word(self):
        """Send all buffered letters to the server as a batch."""
        if not self.letter_buffer:
            return
        try:
            # Save a copy of the buffer and rack in case of error
            self._pending_buffer = self.letter_buffer.copy()
            self._pending_rack = self.tile_rack.copy()
            moves = []
            for (row, col), letter in self.letter_buffer.items():
                # For blank tiles, send the chosen letter (not '?')
                moves.append(f"{row},{col},{letter}")
            batch_move = ";".join(moves)
            # Add blank positions to the move
            if self.blank_tiles:
                blank_positions = []
                for r, c in sorted(self.blank_tiles):
                    blank_positions.extend([str(r), str(c)])
                batch_move = f"{batch_move}|{','.join(blank_positions)}"
                print(f"[DEBUG] Sending blank positions: {blank_positions}")  # Debug log
            self.sock.sendall(batch_move.encode())
            print(f"Sent word batch with {len(self.letter_buffer)} letters: {batch_move}")
            # Do NOT clear the buffer yet; wait for server confirmation
        except Exception as e:
            print(f"Failed to send word: {e}")
            self._return_all_letters()

    def _draw_tiles(self):
        """Request to draw tiles from the server."""
        if not self.game_started:
            self._set_error("Game has not started yet. Wait for all players to be ready.")
            return
            
        if len(self.tile_rack) >= 7:
            self._set_error("Rack is already full!")
            return
        
        if self.tiles_remaining <= 0:
            self._set_error("No tiles remaining in bag!")
            return
        
        try:
            # Calculate how many tiles we need to fill rack
            tiles_needed = 7 - len(self.tile_rack)
            # Request to draw tiles (server will give us what's available)
            draw_request = f"DRAW:{tiles_needed}"
            self.sock.sendall(draw_request.encode())
            print(f"Requested to draw {tiles_needed} tiles")
            
        except Exception as e:
            self._set_error(f"Failed to request tiles: {e}")

    def _send_exchange(self):
        """Send exchange request to server."""
        if not self.tiles_to_exchange:
            self._set_error("No tiles selected for exchange.")
            return
        
        try:
            # Get the letters to exchange
            tiles = [self.tile_rack[i] for i in sorted(self.tiles_to_exchange)]
            exchange_request = f"EXCHANGE:{','.join(tiles)}"
            self.sock.sendall(exchange_request.encode())
            print(f"Requesting to exchange tiles: {tiles}")
            
            # Reset exchange mode
            self.exchange_mode = False
            self.tiles_to_exchange.clear()
            
        except Exception as e:
            print(f"Failed to send exchange request: {e}")
            self._set_error(f"Failed to exchange tiles: {e}")
            # Reset exchange mode on error
            self.exchange_mode = False
            self.tiles_to_exchange.clear()

    def _send_ready(self, ready=True):
        """Send READY/UNREADY to server and update ready state.
        
        Args:
            ready (bool): True to send READY, False to send UNREADY
        """
        try:
            message = "READY" if ready else "UNREADY"
            self.sock.sendall(f"{message}\n".encode())
            # Don't set local ready state - wait for server confirmation
        except Exception as e:
            print(f"Failed to send {message}: {e}")
            self._set_error(f"Failed to send {message}: {e}")

    def _handle_mouse_click(self, pos):
        """Handle mouse click events."""
        x, y = pos
        
        # If showing blank dialog, only handle clicks within the dialog
        if self.showing_blank_dialog:
            if not self.blank_dialog_cancel_button.collidepoint(x, y):
                return
            
        # If showing unseen tiles dialog, only handle clicks within the dialog
        if self.showing_unseen_tiles:
            if not self.unseen_tiles_button.collidepoint(x, y) and not self.unseen_tiles_close_button.collidepoint(x, y):
                return
            
        # Handle connection screen clicks
        if self.connection_screen:
            self._handle_connection_screen_click(pos)
            return
            
        # Handle game end screen
        if self.game_ended:
            if hasattr(self, 'return_to_connection_button') and self.return_to_connection_button.collidepoint(x, y):
                # Disconnect from server and return to connection screen
                try:
                    self._reset_game_state()
                except Exception as e:
                    print(f"Error during disconnect: {e}")
                    # Even if there's an error, try to clean up
                    self._reset_game_state()
                return
            return
            
        # Handle button clicks
        if self._handle_button_click(x, y):
            return
        # Try rack click
        if self._handle_rack_click(x, y):
            return
        # Try board click
        self._handle_board_click(x, y)
        # Check for scroll bar click
        if self.scroll_bar_rect and self.scroll_bar_rect.collidepoint(x, y):
            self.scroll_bar_dragging = True
            self.scroll_bar_offset = y - self.scroll_bar_rect.top

    def _handle_button_click(self, x, y):
        """Handle clicks on buttons."""
        if not self.game_started:
            # Only allow ready button clicks before game starts
            if self.ready_button.collidepoint(x, y):
                if self.ready:
                    # Unready
                    self._send_ready(ready=False)
                else:
                    # Ready
                    self._send_ready(ready=True)
                return True
            return False

        # Handle other buttons only after game starts
        if self.return_button.collidepoint(x, y):
            self._return_all_letters()
            return True
        elif self.send_button.collidepoint(x, y):
            if self.exchange_mode:
                self._send_exchange()
            else:
                self._send_word()
            return True
        elif self.exchange_button.collidepoint(x, y):
            self.exchange_mode = not self.exchange_mode
            self.tiles_to_exchange.clear()
            return True
        elif self.pass_button.collidepoint(x, y):
            if self.game_started and not self.game_ended:
                try:
                    self.sock.sendall(b"PASS\n")  # Add newline to match server's line-based protocol
                except Exception as e:
                    self._set_error(f"Failed to pass turn: {e}")
            return True
        elif self.shuffle_button.collidepoint(x, y):
            if self.game_started and not self.game_ended:
                random.shuffle(self.tile_rack)
            return True
        elif self.unseen_tiles_button.collidepoint(x, y):
            if self.game_started and self.ready and not self.game_ended:
                self.showing_unseen_tiles = not self.showing_unseen_tiles
            return True
        elif hasattr(self, 'unseen_tiles_close_button') and self.unseen_tiles_close_button.collidepoint(x, y):
            self.showing_unseen_tiles = False
            return True
        elif hasattr(self, 'blank_dialog_cancel_button') and self.blank_dialog_cancel_button.collidepoint(x, y):
            self.showing_blank_dialog = False
            # Return the blank tile to the rack
            self.tile_rack.append('?')
            self.blank_pos = None
            return True
        return False

    def _handle_mouse_motion(self, pos):
        """Handle mouse motion events."""
        x, y = pos
        
        # Handle tile dragging
        if self.dragging_tile:
            # Check if we've moved past the drag threshold
            dx = x - self.drag_start_pos[0]
            dy = y - self.drag_start_pos[1]
            distance = (dx * dx + dy * dy) ** 0.5
            
            if distance >= self.drag_threshold:
                if not self.dragging_from_board:
                    # Handle rack tile dragging
                    rack_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 10
                    # Calculate new index based on tile center position
                    tile_center_x = x - self.drag_offset[0]
                    new_index = (tile_center_x - self.MARGIN) // (self.TILE_SIZE + 5)
                    new_index = max(0, min(new_index, len(self.tile_rack) - 1))
                    
                    if new_index != self.drag_current_index:
                        # Swap tiles
                        self.tile_rack[self.drag_current_index], self.tile_rack[new_index] = \
                            self.tile_rack[new_index], self.tile_rack[self.drag_current_index]
                        self.drag_current_index = new_index
        
        # Handle scroll bar dragging
        if self.scroll_bar_dragging and self.scroll_bar_rect:
            log_y = self.MARGIN + 150
            # Calculate new scroll position based on mouse position
            relative_y = y - log_y - 30 - self.scroll_bar_offset
            max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
            scroll_ratio = relative_y / (self.move_log_height - 30 - self.scroll_bar_height)
            new_scroll = int(scroll_ratio * max_scroll)
            self.move_log_scroll = max(0, min(max_scroll, new_scroll))

    def _handle_mouse_release(self):
        """Handle mouse release events."""
        if self.dragging_tile:
            # If we haven't moved much, treat it as a click
            if not self.exchange_mode:
                mouse_x, mouse_y = pygame.mouse.get_pos()
                dx = mouse_x - self.drag_start_pos[0]
                dy = mouse_y - self.drag_start_pos[1]
                distance = (dx * dx + dy * dy) ** 0.5
                
                if distance < self.drag_threshold:
                    # Handle as a click
                    if self.dragging_from_board:
                        # Select the board cell
                        self.selected_board_cell = self.drag_board_pos
                    else:
                        if self.selected_rack_index == self.drag_current_index:
                            self.selected_rack_index = None
                        else:
                            self.selected_rack_index = self.drag_current_index
                            self.selected_board_cell = None
                else:
                    # Handle drag release
                    if self.dragging_from_board:
                        # Check if we're over the rack
                        rack_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 10
                        tile_center_y = mouse_y - self.drag_offset[1]
                        if rack_y <= tile_center_y <= rack_y + self.TILE_SIZE:
                            # Calculate rack position based on tile center
                            tile_center_x = mouse_x - self.drag_offset[0]
                            rack_x = self.MARGIN + len(self.tile_rack) * (self.TILE_SIZE + 5)
                            if tile_center_x >= self.MARGIN and tile_center_x <= rack_x + self.TILE_SIZE + 5:
                                # Calculate drop index based on tile center position
                                drop_index = (tile_center_x - self.MARGIN) // (self.TILE_SIZE + 5)
                                drop_index = max(0, min(drop_index, len(self.tile_rack)))
                                
                                # Return tile to rack at the drop position
                                row, col = self.drag_board_pos
                                letter = self.letter_buffer[(row, col)]
                                # If this was a blank tile, return it as '?'
                                if (row, col) in self.blank_tiles:
                                    self.tile_rack.insert(drop_index, '?')
                                    self.blank_tiles.remove((row, col))
                                else:
                                    self.tile_rack.insert(drop_index, letter)
                                del self.letter_buffer[(row, col)]
                        else:
                            # Check if we're over a valid board position
                            tile_center_x = mouse_x - self.drag_offset[0]
                            tile_center_y = mouse_y - self.drag_offset[1]
                            col = (tile_center_x - self.MARGIN) // self.TILE_SIZE
                            row = (tile_center_y - self.MARGIN) // self.TILE_SIZE
                            if 0 <= row < self.BOARD_SIZE and 0 <= col < self.BOARD_SIZE:
                                # If we're over a different position and it's empty
                                if (row, col) != self.drag_board_pos and self.board[row][col] == '' and (row, col) not in self.letter_buffer:
                                    # Move the tile to the new position
                                    old_row, old_col = self.drag_board_pos
                                    letter = self.letter_buffer[(old_row, old_col)]
                                    del self.letter_buffer[(old_row, old_col)]
                                    # If this was a blank tile, show the dialog again
                                    if (old_row, old_col) in self.blank_tiles:
                                        self.blank_tiles.remove((old_row, old_col))
                                        self.blank_pos = (row, col)
                                        self.showing_blank_dialog = True
                                    else:
                                        self.letter_buffer[(row, col)] = letter
                    else:
                        # Check if we're over the board
                        tile_center_x = mouse_x - self.drag_offset[0]
                        tile_center_y = mouse_y - self.drag_offset[1]
                        col = (tile_center_x - self.MARGIN) // self.TILE_SIZE
                        row = (tile_center_y - self.MARGIN) // self.TILE_SIZE
                        if 0 <= row < self.BOARD_SIZE and 0 <= col < self.BOARD_SIZE:
                            # If the board position is empty
                            if self.board[row][col] == '' and (row, col) not in self.letter_buffer:
                                # Place tile on board
                                letter = self.tile_rack[self.drag_current_index]
                                # Handle blank tile
                                if letter == '?':
                                    self.blank_pos = (row, col)
                                    self.showing_blank_dialog = True
                                    self.tile_rack.pop(self.drag_current_index)
                                else:
                                    self.letter_buffer[(row, col)] = letter
                                    self.tile_rack.pop(self.drag_current_index)
            
            # Reset drag state
            self.dragging_tile = False
            self.drag_start_index = None
            self.drag_current_index = None
            self.drag_offset = (0, 0)
            self.drag_start_pos = (0, 0)
            self.dragging_from_board = False
            self.drag_board_pos = None
            
        self.scroll_bar_dragging = False

    def _handle_keydown(self, key):
        """Handle keyboard events."""
        # Always allow quitting with Q, unless we're in the blank letter dialog
        if key == pygame.K_q and not self.showing_blank_dialog:
            # Quit with Q
            print("\nShutting down client...")
            self.running = False
            return
            
        # Handle tile size adjustment
        if key == pygame.K_PLUS or key == pygame.K_EQUALS:  # Plus or equals key
            self._adjust_tile_size(5)
            return
        elif key == pygame.K_MINUS:  # Minus key
            self._adjust_tile_size(-5)
            return
        elif key == pygame.K_r:
            if not self.game_started:
                if self.ready:
                    # Unready
                    self._send_ready(ready=False)
                else:
                    # Ready
                    self._send_ready(ready=True)
                return

        if not self.game_started:
            self._set_error("Game has not started yet.")
            return
            
        # Handle blank tile letter selection
        if self.showing_blank_dialog:
            if pygame.K_a <= key <= pygame.K_z:
                letter = chr(key).upper()
                # Don't allow selecting '?' as the blank letter
                if letter == '?':
                    return
                row, col = self.blank_pos
                self.letter_buffer[(row, col)] = letter
                self.blank_tiles.add((row, col))  # Mark this as a blank tile
                self.selected_rack_index = None  # Deselect after placing
                self.selected_board_cell = None  # Deselect after placing
                self.showing_blank_dialog = False
                self.blank_pos = None
            elif key == pygame.K_ESCAPE:
                # Return the blank tile to the rack when ESC is pressed
                self.tile_rack.append('?')
                self.showing_blank_dialog = False
                self.blank_pos = None
            return
            
        # Handle ESC for unseen tiles dialog
        if key == pygame.K_ESCAPE and self.showing_unseen_tiles:
            self.showing_unseen_tiles = False
            return
            
        # Handle button shortcuts (only if blank dialog is not showing)
        if not self.showing_blank_dialog:
            if key == pygame.K_r:  # Ready
                self._return_all_letters()
            elif key == pygame.K_d:  # Done
                if self.exchange_mode:
                    self._send_exchange()
                else:
                    self._send_word()
            elif key == pygame.K_e:  # Exchange
                self.exchange_mode = not self.exchange_mode
                self.tiles_to_exchange.clear()
            elif key == pygame.K_p:  # Pass
                if self.game_started and self.ready and not self.game_ended:
                    try:
                        self.sock.sendall(b"PASS\n")
                    except Exception as e:
                        self._set_error(f"Failed to pass turn: {e}")
            elif key == pygame.K_s:  # Shuffle
                if self.game_started and self.ready and not self.game_ended:
                    random.shuffle(self.tile_rack)
            elif key == pygame.K_u:  # Unseen Tiles
                if self.game_started and self.ready and not self.game_ended:
                    self.showing_unseen_tiles = not self.showing_unseen_tiles

        if key == pygame.K_ESCAPE:
            # Cancel selection with ESC
            self.selected_rack_index = None
            self.selected_board_cell = None
        elif key == pygame.K_RETURN or key == pygame.K_KP_ENTER:
            # Send word with Enter
            if not self.letter_buffer:
                self._set_error("No tiles placed.")
                return
            self._send_word()
        elif key == pygame.K_BACKSPACE:
            # Return all letters with Backspace
            self._return_all_letters()

    def _adjust_tile_size(self, delta):
        """Adjust the tile size and update all dependent measurements."""
        new_size = self.TILE_SIZE + delta
        if 20 <= new_size <= 60:  # Limit tile size between 30 and 60
            self.TILE_SIZE = new_size
            # Update dependent measurements
            self.RACK_HEIGHT = self.TILE_SIZE + 20
        
            # Calculate button dimensions to span full width
            button_spacing = int(10 * (self.TILE_SIZE / 40))  # Scale spacing with tile size
            
            # Calculate available width (excluding margins)
            available_width = self.WIDTH - (2 * self.MARGIN)
            
            # Calculate button width to fit all buttons with spacing
            num_buttons = 6  # Total number of buttons
            total_spacing = button_spacing * (num_buttons - 1)
            button_width = (available_width - total_spacing) // num_buttons
            button_height = int(button_width * 0.35)  # Always 35% of button width

            self.WIDTH = self.TILE_SIZE * self.BOARD_SIZE + self.MARGIN * 2 + self.PLAYER_LIST_WIDTH + 20
            self.HEIGHT = (self.TILE_SIZE * self.BOARD_SIZE + self.MARGIN * 2 + 
                          self.RACK_HEIGHT + self.INFO_HEIGHT + button_height + 
                          self.BUTTON_MARGIN * 3 + 40)
            
            # Resize the window
            self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
            
            # Update font sizes
            self._update_font_sizes()
            
            # Recalculate move log height
            button_y = (self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 
                       self.RACK_HEIGHT + self.INFO_HEIGHT + 15 + 36 + 20)
            log_y = self.MARGIN + 150
            self.move_log_height = button_y - log_y - self.TILE_SIZE
            
            # Update button positions
            self._setup_buttons()
            
            # Show feedback
            self._set_error(f"Tile size: {self.TILE_SIZE}")

    def _calculate_move_log_content_height(self):
        """Calculate the total height of the move log content."""
        content_height = 0
        for move in self.move_log:
            if 'words' in move:  # Regular move
                content_height += 20
                for word_info in move['words']:
                    # Word tiles line
                    content_height += 25
                    
                    # Definition lines
                    definition = word_info['definition']
                    words = definition.split()
                    lines = []
                    current_line = []
                    for word in words:
                        if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                            current_line.append(word)
                        else:
                            lines.append(' '.join(current_line))
                            current_line = [word]
                    if current_line:
                        lines.append(' '.join(current_line))
                    content_height += len(lines) * 15
                    
                    # Space after definition
                    content_height += 2
                
                # Space between moves
                content_height += 2
            elif move.get('type') == 'pass':  # Pass move
                content_height += 15
                content_height += 2  # Space after pass move
            elif move.get('type') == 'game_end':  # Game end move
                content_height += 20
                # Add height for each player's score
                content_height += len(move.get('scores', {})) * 20
                content_height += 2  # Space after game end
            elif move.get('type') == 'exchange':  # Exchange move
                # Calculate height for wrapped exchange text
                text = f"{move['username']}: Exchanged tiles"
                words = text.split()
                lines = []
                current_line = []
                for word in words:
                    if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                        current_line.append(word)
                    else:
                        lines.append(' '.join(current_line))
                        current_line = [word]
                if current_line:
                    lines.append(' '.join(current_line))
                content_height += len(lines) * 15  # Height for wrapped lines
                content_height += 2  # Space after exchange move
        
        self.move_log_content_height = content_height
        # Ensure scroll position is within bounds
        max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
        self.move_log_scroll = min(max_scroll, max(0, self.move_log_scroll))

    def _handle_mouse_wheel(self, y):
        """Handle mouse wheel scrolling."""
        # Check if mouse is over move log area
        log_x = self.WIDTH - self.PLAYER_LIST_WIDTH - 20
        log_y = self.MARGIN + 150
        mouse_pos = pygame.mouse.get_pos()
        if (log_x <= mouse_pos[0] <= log_x + self.PLAYER_LIST_WIDTH and 
            log_y <= mouse_pos[1] <= log_y + self.move_log_height):
            
            # Calculate max scroll using stored content height
            max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
            
            # Update scroll position with bounds checking
            new_scroll = self.move_log_scroll - y * 30
            self.move_log_scroll = max(0, min(max_scroll, new_scroll))

    def run(self):
        """Main game loop."""
        print("[DEBUG] Starting main game loop")
        # Draw initial connection screen
        self._draw_connection_screen()
        pygame.display.flip()
        
        try:
            while self.running:
                for event in pygame.event.get():
                    if event.type == pygame.QUIT:
                        print("[DEBUG] Received pygame.QUIT event")
                        self.running = False
                    elif event.type == pygame.MOUSEBUTTONDOWN:
                        if self.connection_screen:
                            self._handle_connection_screen_click(event.pos)
                        else:
                            self._handle_mouse_click(event.pos)
                    elif event.type == pygame.MOUSEBUTTONUP:
                        if not self.game_ended:  # Only handle mouse up if game hasn't ended
                            self._handle_mouse_release()
                    elif event.type == pygame.MOUSEMOTION:
                        if not self.game_ended:  # Only handle mouse motion if game hasn't ended
                            self._handle_mouse_motion(event.pos)
                    elif event.type == pygame.MOUSEWHEEL:
                        if not self.game_ended:  # Only handle mouse wheel if game hasn't ended
                            self._handle_mouse_wheel(event.y)
                    elif event.type == pygame.KEYDOWN:
                        if self.connection_screen:
                            self._handle_connection_screen_key(event)
                        else:
                            self._handle_keydown(event.key)
                
                # Auto-clear error message after 3 seconds
                if self.error_message and pygame.time.get_ticks() - self.error_time > 3000:
                    self.error_message = None
                
                # Draw appropriate screen
                if self.connection_screen:
                    self._draw_connection_screen()
                else:
                    self.draw_board()
                
                # Update the display
                pygame.display.flip()
                self.clock.tick(60)
        except KeyboardInterrupt:
            print("\nKeyboard interrupt received, shutting down client...")
            self.running = False
        except Exception as e:
            print(f"[ERROR] Unexpected error in main game loop: {e}")
            traceback.print_exc()
        finally:
            print("[DEBUG] Entering cleanup in main game loop")
            self._cleanup()

    def _cleanup(self):
        """Clean up resources before exiting."""
        if hasattr(self, '_cleaned') and self._cleaned:
            print("[DEBUG] Cleanup already performed, skipping")
            return
        print("[DEBUG] Starting cleanup procedure")
        self._cleaned = True
        print("Cleaning up resources...")
        
        # First stop the network thread
        self.running = False
        if self.network_thread and self.network_thread.is_alive():
            print("[DEBUG] Waiting for network thread to finish")
            self.network_thread.join(timeout=2.0)
            print("[DEBUG] Network thread finished")
        
        # Then handle socket cleanup
        if self.sock:
            try:
                print("[DEBUG] Attempting to send disconnect message")
                try:
                    self.sock.sendall("DISCONNECT\n".encode())
                    print("[DEBUG] Disconnect message sent successfully")
                except Exception as e:
                    print(f"[ERROR] Failed to send disconnect message: {e}")
                print("[DEBUG] Closing socket")
                self.sock.close()
                print("[DEBUG] Socket closed successfully")
            except Exception as e:
                print(f"[ERROR] Error during socket cleanup: {e}")
            finally:
                self.sock = None
        
        print("[DEBUG] Quitting pygame")
        pygame.quit()
        print("Client shutdown complete")
        sys.exit(0)

    def _send_initial_data(self, conn):
        """Send board and rack to new/reconnected player."""
        try:
            # Send board
            initial_data = json.dumps(self.board).encode() + b'\n'
            conn.sendall(initial_data)
            
            # Send rack update
            self._send_rack_update(conn)
        except Exception as e:
            print(f"[ERROR] Failed to send initial data: {e}")

    def _send_rack_update(self, conn):
        """Send a player their current rack."""
        try:
            rack_data = {
                'type': 'rack_update',
                'rack': self.tile_rack,
                'tiles_remaining': self.tiles_remaining
            }
            message = json.dumps(rack_data).encode() + b'\n'
            conn.sendall(message)
        except Exception as e:
            print(f"[ERROR] Failed to send rack update: {e}")

    def _set_error(self, msg):
        """Set an error message and schedule it to clear after 3 seconds."""
        self.error_message = msg
        self.error_time = pygame.time.get_ticks()

    def draw_move_log(self):
        """Draw the move log box."""
        # Position below player list
        log_x = self.WIDTH - self.PLAYER_LIST_WIDTH - 20
        log_y = self.MARGIN + 150  # Below player list
        
        # Calculate content height before drawing
        self._calculate_move_log_content_height()
        
        # Draw background
        pygame.draw.rect(self.screen, (240, 240, 240), 
                        (log_x, log_y, self.PLAYER_LIST_WIDTH, self.move_log_height))
        pygame.draw.rect(self.screen, (150, 150, 150), 
                        (log_x, log_y, self.PLAYER_LIST_WIDTH, self.move_log_height), 1)
        
        # Draw title
        title_font = pygame.font.SysFont(None, 20)
        title = title_font.render("Move Log", True, (0, 0, 0))
        title_rect = title.get_rect(centerx=log_x + self.PLAYER_LIST_WIDTH // 2, y=log_y + 5)
        self.screen.blit(title, title_rect)
        
        # Use stored content height
        max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
        self.move_log_scroll = min(max_scroll, max(0, self.move_log_scroll))
        
        # Draw scroll bar if content exceeds box height
        if self.move_log_content_height > self.move_log_height - 30:  # Account for title
            # Calculate scroll bar height and position
            visible_height = self.move_log_height - 30
            scroll_bar_height = max(30, int(visible_height * (visible_height / self.move_log_content_height)))
            scroll_bar_y = log_y + 30 + (self.move_log_scroll * (visible_height - scroll_bar_height) / (self.move_log_content_height - visible_height))
            
            # Store scroll bar rectangle for mouse interaction
            self.scroll_bar_rect = pygame.Rect(log_x + self.PLAYER_LIST_WIDTH - 15, scroll_bar_y, 10, scroll_bar_height)
            self.scroll_bar_height = scroll_bar_height
            
            # Draw scroll bar
            pygame.draw.rect(self.screen, (200, 200, 200), self.scroll_bar_rect)
            pygame.draw.rect(self.screen, (100, 100, 100), self.scroll_bar_rect, 1)
        
        # Set clipping region for move log content
        clip_rect = pygame.Rect(log_x, log_y + 30, self.PLAYER_LIST_WIDTH - 15, self.move_log_height - 30)  # Reduced width by 5 pixels
        self.screen.set_clip(clip_rect)
        
        # Initialize y_offset
        y_offset = log_y + 30 - self.move_log_scroll
        
        # Draw moves
        for i, move in enumerate(self.move_log):
            # Calculate move height
            move_height = 0  # Player name and points
            if 'words' in move:  # Regular move
                move_height += 20
                for word_info in move['words']:
                    move_height += 25  # Word tiles
                    # Add height for definition lines
                    definition = word_info['definition']
                    words = definition.split()
                    lines = []
                    current_line = []
                    for word in words:
                        if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                            current_line.append(word)
                        else:
                            lines.append(' '.join(current_line))
                            current_line = [word]
                    if current_line:
                        lines.append(' '.join(current_line))
                    move_height += len(lines) * 15
                    move_height += 2  # Space after definition
                move_height += 2  # Space between moves
            elif move.get('type') == 'pass':  # Pass move
                move_height += 15  # Pass move line
                move_height += 2  # Space after pass move
            elif move.get('type') == 'game_end':  # Game end move
                move_height += 20  # Game end line
                move_height += 2  # Space after game end
            elif move.get('type') == 'exchange':  # Exchange move
                # Draw exchange text
                text = f"{move['username']}: Exchanged tiles"
                words = text.split()
                lines = []
                current_line = []
                for word in words:
                    if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                        current_line.append(word)
                    else:
                        lines.append(' '.join(current_line))
                        current_line = [word]
                if current_line:
                    lines.append(' '.join(current_line))
                move_height += len(lines) * 15
                move_height += 2  # Space after exchange move
            
            # Skip if this move would be completely above the visible area
            if y_offset + move_height < log_y + 30:
                y_offset += move_height
                continue
                
            # Skip if this move would be completely below the visible area
            if y_offset > log_y + self.move_log_height:
                y_offset += move_height
                continue
            
            # Draw move number
            move_num = f"{i + 1}"
            # BLUE (40, 120, 215)
            num_surface = self.info_font.render(move_num, True, (255, 105, 180))  # Pink color
            if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                self.screen.blit(num_surface, (log_x + 5, y_offset))
            
            # Draw move content based on type
            if 'words' in move:  # Regular move
                player_text = f"{move['username']}: "
                player_surface = self.info_font.render(player_text, True, (0, 0, 0))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    self.screen.blit(player_surface, (log_x + 25, y_offset))
                
                # Draw points number in purple
                points_num = f"{move['total_points']}"
                points_surface = self.info_font.render(points_num, True, (0, 74, 128))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    points_rect = points_surface.get_rect(topleft=(log_x + 25 + player_surface.get_width(), y_offset))
                    self.screen.blit(points_surface, points_rect)
                
                # Draw "pts" in black
                pts_text = " pts"
                pts_surface = self.info_font.render(pts_text, True, (0, 0, 0))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    pts_rect = pts_surface.get_rect(topleft=(points_rect.right, y_offset))
                    self.screen.blit(pts_surface, pts_rect)
                
                y_offset += 20
                
                # Draw each word
                for word_info in move['words']:
                    # Calculate word height
                    word_height = 25  # Word tiles
                    definition = word_info['definition']
                    words = definition.split()
                    lines = []
                    current_line = []
                    for word in words:
                        if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                            current_line.append(word)
                        else:
                            lines.append(' '.join(current_line))
                            current_line = [word]
                    if current_line:
                        lines.append(' '.join(current_line))
                    word_height += len(lines) * 15
                    word_height += 2  # Space after definition
                    
                    # Skip if this word would be completely below the visible area
                    if y_offset + word_height < log_y + 30:
                        y_offset += word_height
                        continue
                    
                    # Skip if this word would be completely above the visible area
                    if y_offset > log_y + self.move_log_height:
                        y_offset += word_height
                        continue
                    
                    # Draw word with colored tiles
                    x_offset = log_x + 10
                    for row, col, letter, square_type in word_info['positions']:
                        # Determine tile color based on square type
                        if square_type == 'DL':
                            color = self.SPECIAL_COLORS['DL']
                        elif square_type == 'TL':
                            color = self.SPECIAL_COLORS['TL']
                        elif square_type == 'DW':
                            color = self.SPECIAL_COLORS['DW']
                        elif square_type == 'TW':
                            color = self.SPECIAL_COLORS['TW']
                        else:
                            color = self.LETTER_COLORS['placed']
                        
                        # Draw tile
                        tile_rect = pygame.Rect(x_offset, y_offset, 20, 20)
                        if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                            pygame.draw.rect(self.screen, color, tile_rect)
                            pygame.draw.rect(self.screen, (0, 0, 0), tile_rect, 1)
                            
                            # Draw letter
                            text_color = self.LETTER_TEXT_COLORS['blank'] if (row, col) in self.blank_tiles else self.LETTER_TEXT_COLORS['normal']
                            letter_surface = self.info_font.render(letter, True, text_color)
                            letter_rect = letter_surface.get_rect(center=tile_rect.center)
                            self.screen.blit(letter_surface, letter_rect)
                        
                        x_offset += 22
                    
                    # Draw word score after the tiles
                    score_text = f" {word_info['score']}"
                    score_surface = self.info_font.render(score_text, True, (128, 0, 128))  # Purple color
                    if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                        self.screen.blit(score_surface, (x_offset, y_offset + 5))
                    
                    # Draw definition
                    y_offset += 25
                    definition = word_info['definition']
                    # Split definition into multiple lines if too long
                    words = definition.split()
                    lines = []
                    current_line = []
                    for word in words:
                        if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                            current_line.append(word)
                        else:
                            lines.append(' '.join(current_line))
                            current_line = [word]
                    if current_line:
                        lines.append(' '.join(current_line))
                    
                    for line in lines:
                        # Always render the line to maintain proper spacing
                        def_surface = self.info_font.render(line, True, (100, 100, 100))
                        # Only blit if it's in the visible area
                        if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                            self.screen.blit(def_surface, (log_x + 10, y_offset))
                        y_offset += 15
                    
                    y_offset += 2  # Space after definition
                
                y_offset += 2

            elif move.get('type') == 'pass':  # Pass move
                player_text = f"{move['username']}: Passed turn"
                player_surface = self.info_font.render(player_text, True, (0, 0, 0))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    self.screen.blit(player_surface, (log_x + 25, y_offset))
                y_offset += 15
                y_offset += 2  # Space after pass move
            elif move.get('type') == 'game_end':  # Game end move
                # Draw final scores
                scores_text = "Final Scores:"
                scores_surface = self.info_font.render(scores_text, True, (0, 0, 0))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    self.screen.blit(scores_surface, (log_x + 25, y_offset))
                y_offset += 20
                
                # Draw each player's score
                for username, score in move.get('scores', {}).items():
                    score_text = f"{username}: {score} points"
                    score_surface = self.info_font.render(score_text, True, (0, 0, 0))
                    if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                        self.screen.blit(score_surface, (log_x + 35, y_offset))
                    y_offset += 20
                y_offset += 2  # Space after game end
            elif move.get('type') == 'exchange':  # Exchange move
                # Draw exchange text
                text = f"{move['username']}: Exchanged tiles"
                words = text.split()
                lines = []
                current_line = []
                for word in words:
                    if len(' '.join(current_line + [word])) * 6 < self.PLAYER_LIST_WIDTH - 40:
                        current_line.append(word)
                    else:
                        lines.append(' '.join(current_line))
                        current_line = [word]
                if current_line:
                    lines.append(' '.join(current_line))
                move_height = len(lines) * 15  # Height for wrapped lines
                move_height += 2  # Space after exchange move
                # Draw exchange text
                for line in lines:
                    player_surface = self.info_font.render(line, True, (0, 0, 0))
                    if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                        self.screen.blit(player_surface, (log_x + 25, y_offset))
                    y_offset += 15
                y_offset += 2  # Space after exchange move
        
        # Reset clipping
        self.screen.set_clip(None)

    def _get_word_at_position(self, row, col, horizontal=True):
        """Get the word at a given position, including any extensions."""
        word = []
        positions = []
        if horizontal:
            # Look left
            c = col
            while c >= 0 and (self.board[row][c] != '' or (row, c) in self.letter_buffer):
                letter = self.board[row][c] if self.board[row][c] != '' else self.letter_buffer.get((row, c))
                word.insert(0, letter)
                positions.insert(0, (row, c))
                c -= 1
            # Look right
            c = col + 1
            while c < self.BOARD_SIZE and (self.board[row][c] != '' or (row, c) in self.letter_buffer):
                letter = self.board[row][c] if self.board[row][c] != '' else self.letter_buffer.get((row, c))
                word.append(letter)
                positions.append((row, c))
                c += 1
        else:
            # Look up
            r = row
            while r >= 0 and (self.board[r][col] != '' or (r, col) in self.letter_buffer):
                letter = self.board[r][col] if self.board[r][col] != '' else self.letter_buffer.get((r, col))
                word.insert(0, letter)
                positions.insert(0, (r, col))
                r -= 1
            # Look down
            r = row + 1
            while r < self.BOARD_SIZE and (self.board[r][col] != '' or (r, col) in self.letter_buffer):
                letter = self.board[r][col] if self.board[r][col] != '' else self.letter_buffer.get((r, col))
                word.append(letter)
                positions.append((r, col))
                r += 1
        return ''.join(word), positions if len(word) >= 2 else None

    def _get_all_words(self, moves):
        """Get all words that would be created by the current buffer."""
        words = []
        # Create a temporary board with the moves
        temp_board = [row[:] for row in self.board]
        for (row, col), letter in self.letter_buffer.items():
            temp_board[row][col] = letter
        
        # Check horizontal words
        for (row, col), _ in self.letter_buffer.items():
            word, positions = self._get_word_at_position(row, col, True)
            if positions:
                words.append((word, positions, True))
        
        # Check vertical words
        for (row, col), _ in self.letter_buffer.items():
            word, positions = self._get_word_at_position(row, col, False)
            if positions:
                words.append((word, positions, False))
        
        return words

    def _calculate_word_score(self, word, positions):
        """Calculate the score for a word, including special squares."""
        total_score = 0
        word_mult = 1
        
        # Create a temporary set of blank positions that includes both existing and new blanks
        temp_blanks = self.blank_tiles.copy()
        
        # Check if this is the primary word (contains all buffered letters)
        is_primary_word = all((row, col) in positions for row, col in self.letter_buffer)
        
        for row, col in positions:
            letter = self.board[row][col] if self.board[row][col] != '' else self.letter_buffer.get((row, col))
            # Check if this is a blank tile
            is_blank = (row, col) in temp_blanks
            # Always score 0 for blank tiles
            letter_score = self.LETTER_VALUES.get('?') if is_blank else self.LETTER_VALUES.get(letter.upper(), 0)
            square_type = self.special_tiles[row][col]
            
            # Check if this is a new tile (part of the current buffer)
            is_new_tile = (row, col) in self.letter_buffer
            
            if is_new_tile:  # Only apply letter multipliers to new tiles
                # Apply letter multipliers only to new tiles
                if square_type == 'DL':
                    letter_score *= 2
                elif square_type == 'TL':
                    letter_score *= 3
                # Apply word multipliers to all tiles
                if square_type == 'DW' or square_type == '*':  # Center star is also double word
                    word_mult *= 2
                elif square_type == 'TW':
                    word_mult *= 3
            
            total_score += letter_score
        
        # Apply word multiplier
        total_score *= word_mult
        
        # Add bingo bonus (50 points) only for primary words that use all 7 tiles
        if is_primary_word and len(self.letter_buffer) == 7:
            total_score += 50
        
        return total_score

    def _load_dictionary(self):
        """Load the Scrabble dictionary."""
        try:
            with open('assets/dictionary/words_with_definitions.txt', 'r', encoding='utf-8') as f:
                # Skip the header line
                next(f)
                for line in f:
                    # Split on tab and take just the word
                    word = line.strip().split('\t')[0].strip().upper()
                    self.dictionary.add(word)
            print(f"[DICTIONARY] Loaded {len(self.dictionary)} words")
        except Exception as e:
            print(f"[ERROR] Failed to load dictionary: {e}")
            sys.exit(1)

    def _is_valid_word(self, word):
        """Check if a word is in the dictionary."""
        return word.upper() in self.dictionary

    def _draw_blank_dialog(self):
        """Draw the blank tile letter selection dialog."""
        # Draw semi-transparent overlay
        overlay = pygame.Surface((self.WIDTH, self.HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 128))
        self.screen.blit(overlay, (0, 0))
        
        # Draw dialog box
        dialog_width = 300
        dialog_height = 200  # Increased height to accommodate buttons
        dialog_x = (self.WIDTH - dialog_width) // 2
        dialog_y = (self.HEIGHT - dialog_height) // 2
        
        pygame.draw.rect(self.screen, (255, 255, 255), 
                       (dialog_x, dialog_y, dialog_width, dialog_height))
        pygame.draw.rect(self.screen, (0, 0, 0), 
                       (dialog_x, dialog_y, dialog_width, dialog_height), 2)
        
        # Create fixed-size fonts for the dialog
        title_font = pygame.font.SysFont(None, 24)  # Fixed size for title
        letter_font = pygame.font.SysFont(None, 28)  # Font for blank tile letter
        value_font = pygame.font.SysFont(None, 16)  # Font for tile value
        button_font = pygame.font.SysFont(None, 20) # Fixed size for button text
        
        # Draw instructions
        text = title_font.render("Type a letter for the blank tile", True, (0, 0, 0))
        text_rect = text.get_rect(centerx=dialog_x + dialog_width//2, 
                                y=dialog_y + 20)
        self.screen.blit(text, text_rect)
        
        # Draw blank tile
        tile_size = 40
        tile_x = dialog_x + (dialog_width - tile_size) // 2
        tile_y = dialog_y + 50
        
        # Draw tile background
        pygame.draw.rect(self.screen, (255, 255, 255), (tile_x, tile_y, tile_size, tile_size))  # Purple background
        pygame.draw.rect(self.screen, (0, 0, 0), (tile_x, tile_y, tile_size, tile_size), 2)
        
        # Draw question mark in white
        question_mark = letter_font.render("?", True, (128, 0, 128))
        question_rect = question_mark.get_rect(center=(tile_x + tile_size//2, tile_y + tile_size//2))
        self.screen.blit(question_mark, question_rect)
        
        # Draw point value (0) in white
        value_text = value_font.render(str(self.LETTER_VALUES.get('?')), True, (80, 80, 80))
        value_rect = value_text.get_rect(bottomright=(tile_x + tile_size - 3, tile_y + tile_size - 2))
        self.screen.blit(value_text, value_rect)

        # Draw cancel button
        cancel_button = pygame.Rect(dialog_x + (dialog_width - 100) // 2,
                                  dialog_y + dialog_height - 50,
                                  100, 30)
        pygame.draw.rect(self.screen, (200, 200, 200), cancel_button)
        pygame.draw.rect(self.screen, (0, 0, 0), cancel_button, 2)
        
        cancel_text = button_font.render("Cancel", True, (0, 0, 0))
        cancel_rect = cancel_text.get_rect(center=cancel_button.center)
        self.screen.blit(cancel_text, cancel_rect)

        # Store button rectangle for click detection
        self.blank_dialog_cancel_button = cancel_button

    def _draw_unseen_tiles_dialog(self):
        """Draw the dialog showing unseen tiles."""
        if not self.showing_unseen_tiles:
            return

        # Calculate dialog dimensions
        dialog_width = 400
        dialog_height = 300
        dialog_x = (self.WIDTH - dialog_width) // 2
        dialog_y = (self.HEIGHT - dialog_height) // 2

        # Draw dialog background
        pygame.draw.rect(self.screen, (255, 255, 255), (dialog_x, dialog_y, dialog_width, dialog_height))
        pygame.draw.rect(self.screen, (0, 0, 0), (dialog_x, dialog_y, dialog_width, dialog_height), 2)

        # Draw title
        title_font = pygame.font.SysFont('Arial', 24, bold=True)
        title_text = title_font.render("Unseen Tiles", True, (0, 0, 0))
        title_rect = title_text.get_rect(centerx=dialog_x + dialog_width//2, y=dialog_y + 20)
        self.screen.blit(title_text, title_rect)

        # Draw close button
        close_button_rect = pygame.Rect(dialog_x + dialog_width - 100, dialog_y + dialog_height - 40, 80, 30)
        pygame.draw.rect(self.screen, (200, 200, 200), close_button_rect)
        pygame.draw.rect(self.screen, (0, 0, 0), close_button_rect, 1)
        close_font = pygame.font.SysFont('Arial', 20, bold=True)
        close_text = close_font.render("Close", True, (0, 0, 0))
        close_text_rect = close_text.get_rect(center=close_button_rect.center)
        self.screen.blit(close_text, close_text_rect)

        # Draw tile distribution in a grid
        if hasattr(self, 'tile_distribution'):
            # Create a copy of the distribution and subtract tiles in rack
            available_tiles = dict(self.tile_distribution)
            for tile in self.tile_rack:
                if tile in available_tiles:
                    available_tiles[tile] = max(0, available_tiles[tile] - 1)

            # Create fonts for letter and count
            letter_font = pygame.font.SysFont('Arial', 20)  # Standard letter font
            value_font = pygame.font.SysFont('Arial', 12)  # Small font for tile values
            count_font = pygame.font.SysFont('Arial', 16)  # Font for count numbers
            
            tile_size = 35  # Reduced tile size
            spacing = 8  # Reduced spacing
            tiles_per_row = 9  # Increased tiles per row
            x_start = dialog_x + (dialog_width - (tiles_per_row * (tile_size + spacing) - spacing)) // 2  # Center the grid
            y_start = dialog_y + 60

            # Sort tiles by letter
            sorted_tiles = sorted(available_tiles.items(), key=lambda x: x[0])

            for i, (tile, count) in enumerate(sorted_tiles):
                if count > 0:  # Only show tiles that are still available
                    row = i // tiles_per_row
                    col = i % tiles_per_row
                    x = x_start + col * (tile_size + spacing)
                    y = y_start + row * (tile_size + spacing + 20)

                    # Draw tile background
                    pygame.draw.rect(self.screen, (200, 200, 200), (x, y, tile_size, tile_size))
                    pygame.draw.rect(self.screen, (0, 0, 0), (x, y, tile_size, tile_size), 1)

                    # Draw tile letter
                    letter_text = letter_font.render(tile, True, (0, 0, 0))
                    letter_rect = letter_text.get_rect(center=(x + tile_size//2, y + tile_size//2))
                    self.screen.blit(letter_text, letter_rect)

                    # Draw tile value (gray)
                    value = self.LETTER_VALUES.get(tile.upper(), 0)
                    value_text = value_font.render(str(value), True, (80, 80, 80))
                    value_rect = value_text.get_rect(bottomright=(x + tile_size - 3, y + tile_size - 2))
                    self.screen.blit(value_text, value_rect)

                    # Draw count below tile (blue)
                    count_text = count_font.render(str(count), True, (0, 0, 255))
                    count_rect = count_text.get_rect(center=(x + tile_size//2, y + tile_size + 10))
                    self.screen.blit(count_text, count_rect)

        # Store close button rect for click detection
        self.unseen_tiles_close_button = close_button_rect

    def _reset_game_state(self):
        """Reset all game state variables and disconnect from server if connected."""
        # Try to disconnect from server if connected
        if self.sock:
            try:
                self.sock.sendall("DISCONNECT\n".encode())
            except:
                pass
            try:
                self.sock.close()
            except:
                pass
            self.sock = None

        # Reset all game state
        self.connection_screen = True
        self.game_ended = False
        self.game_started = False
        self.players = []
        self.tile_rack = []
        self.move_log = []
        self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
        self.letter_buffer.clear()
        self.blank_tiles.clear()

def main():
    """Entry point for the application."""
    client = ScrabbleClient()
    client.run()


if __name__ == "__main__":
    main()