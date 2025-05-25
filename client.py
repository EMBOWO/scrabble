import pygame
import socket
import threading
import json
import sys
import random
import traceback


class ScrabbleClient:
    # Class constants
    TILE_SIZE = 30
    BOARD_SIZE = 15
    MARGIN = 40
    RACK_HEIGHT = TILE_SIZE + 20
    INFO_HEIGHT = 60
    BUTTON_HEIGHT = 30
    BUTTON_MARGIN = 10
    PLAYER_LIST_WIDTH = 200  # Width for player list
    WIDTH = TILE_SIZE * BOARD_SIZE + MARGIN * 2 + PLAYER_LIST_WIDTH + 20  # Added width for player list
    HEIGHT = TILE_SIZE * BOARD_SIZE + MARGIN * 2 + RACK_HEIGHT + INFO_HEIGHT + BUTTON_HEIGHT + BUTTON_MARGIN * 3 + 40  # slightly taller
    
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

    def __init__(self):
        """Initialize the Scrabble client."""
        pygame.init()
        self.screen = pygame.display.set_mode((self.WIDTH, self.HEIGHT))
        pygame.display.set_caption("Scrabble Client with Tile Drawing")
        self.font = pygame.font.SysFont(None, 24)
        self.button_font = pygame.font.SysFont(None, 20)
        self.info_font = pygame.font.SysFont(None, 18)
        self.title_font = pygame.font.SysFont(None, 36)  # Larger font for game end screen
        self.clock = pygame.time.Clock()
        self.state_lock = threading.Lock()
        
        # Game state
        self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
        self.tile_rack = []  # Will be populated from server
        self.selected_rack_index = None
        self.selected_board_cell = None
        self.tiles_remaining = 0  # Track tiles left in bag
        self.players = []  # Initialize players list
        self.exchange_mode = False  # Track if we're in exchange mode
        self.tiles_to_exchange = set()  # Track tiles selected for exchange
        
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
        self.move_log_height = button_y - (self.MARGIN + 150)  # Height from player list to buttons
        self.scroll_bar_rect = None  # Store scroll bar rectangle
        self.scroll_bar_dragging = False  # Track if scroll bar is being dragged
        self.scroll_bar_height = 0  # Height of the scroll bar
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
        self.error_message = None  # For displaying error messages
        self.error_time = 0  # For auto-clearing error messages
        self._connect_to_server()

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
        button_width = 100
        button_spacing = 10
        self.return_button = pygame.Rect(
            self.MARGIN, 
            button_y, 
            button_width, 
            self.BUTTON_HEIGHT
        )
        self.send_button = pygame.Rect(
            self.MARGIN + button_width + button_spacing, 
            button_y, 
            button_width, 
            self.BUTTON_HEIGHT
        )
        self.exchange_button = pygame.Rect(
            self.MARGIN + 2 * (button_width + button_spacing),
            button_y,
            button_width,
            self.BUTTON_HEIGHT
        )
        self.ready_button = pygame.Rect(
            self.MARGIN + 3 * (button_width + button_spacing),
            button_y,
            button_width,
            self.BUTTON_HEIGHT
        )
        # Add shuffle button to the right of the pass button
        self.shuffle_button = pygame.Rect(
            self.MARGIN + 3 * (button_width + button_spacing),
            button_y,
            button_width,
            self.BUTTON_HEIGHT
        )
        # Add pass button to the right of the ready button
        self.pass_button = pygame.Rect(
            self.MARGIN + 4 * (button_width + button_spacing),
            button_y,
            button_width,
            self.BUTTON_HEIGHT
        )

    def _connect_to_server(self):
        """Robust connection handling with timeout."""
        while True:  # Keep trying until we get a valid username
            try:
                if self.sock:
                    self.sock.close()
                    self.sock = None
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.sock.settimeout(10.0)
                
                # Get server IP address
                server_ip = input("Enter server IP address (press Enter for localhost): ").strip()
                if not server_ip:
                    server_ip = 'localhost'
                self.HOST = server_ip
                
                print(f"[DEBUG] Attempting to connect to {self.HOST}:{self.PORT}")
                try:
                    self.sock.connect((self.HOST, self.PORT))
                    print("[DEBUG] Socket connection successful")
                except ConnectionRefusedError:
                    print("[ERROR] Connection refused. Is the server running?")
                    raise
                except socket.gaierror:
                    print("[ERROR] Invalid IP address or hostname")
                    raise
                except Exception as e:
                    print(f"[ERROR] Connection failed: {str(e)}")
                    raise
                
                username = input("Enter your username: ").strip()
                if not username:
                    username = f"Player_{random.randint(1000,9999)}"
                print(f"[DEBUG] Sending username: {username}")
                self.sock.sendall(f"USERNAME:{username}\n".encode())
                response = self._receive_line()
                print(f"[DEBUG] Server response: {response}")
                if response.startswith("ERROR"):
                    print(f"[ERROR] Server rejected connection: {response[6:]}")
                    continue
                elif response != "OK:Username accepted":
                    print("[ERROR] Unexpected server response")
                    continue
                print("[DEBUG] Connected successfully! Waiting for game data...")
                # Start network thread after successful connection
                if self.network_thread is None or not self.network_thread.is_alive():
                    self.network_thread = threading.Thread(target=self._receive_messages, daemon=True)
                    self.network_thread.start()
                return  # Successfully connected, exit the loop
            except socket.timeout:
                print("[ERROR] Connection timed out - is the server running?")
                if self.sock:
                    self.sock.close()
                    self.sock = None
                sys.exit(1)
            except Exception as e:
                print(f"[ERROR] Connection failed: {str(e)}")
                if self.sock:
                    self.sock.close()
                    self.sock = None
                sys.exit(1)

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
            try:
                data = self.sock.recv(4096).decode()
                if not data:
                    print("Connection closed by server")
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
                                    print("Server is shutting down, closing client...")
                                    self.running = False
                                    self._cleanup()
                                    return
                            elif line.startswith("OK:"):
                                print(f"Server confirmation: {line[3:]}")
                        except Exception as e:
                            print(f"Error processing message: {e}")
                            print(f"Raw message was: {repr(line)}")
            except socket.timeout:
                continue
            except Exception as e:
                if self.running:
                    print(f"Network error: {e}")
                break

    def _process_server_message(self, message):
        """Process a message received from the server."""
        print(f"Processing message: {repr(message)}")
        try:
            message = message.strip()
            try:
                data = json.loads(message)
                print(f"Parsed JSON data: {data}")
                if isinstance(data, dict) and data.get("type") == "game_end":
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
                elif isinstance(data, dict) and data.get("type") == "players":
                    print("Received players update")
                    self.players = data["players"]
                    # Update game_started from server
                    if "game_started" in data:
                        self.game_started = data["game_started"]
                        if self.game_started:
                            self.ready = True
                    self.draw_player_list()
                elif isinstance(data, dict) and data.get("type") == "move_log":
                    print("Received move log update")
                    self.move_log = data["moves"]
                    self._calculate_move_log_content_height()  # Calculate height after updating moves
                    # Scroll to bottom when new moves are added
                    max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
                    self.move_log_scroll = max_scroll
                elif isinstance(data, dict) and data.get("type") == "rack_update":
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
                elif isinstance(data, dict) and data.get("type") == "game_start":
                    print("Game started!")
                    self.game_started = True
                    self.ready = True
                    # Request rack update when game starts
                    try:
                        self.sock.sendall(b"GET_RACK")
                    except Exception as e:
                        print(f"Failed to request rack update: {e}")
                elif isinstance(data, dict) and data.get("type") == "board_update":
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
                        print("Server is shutting down, closing client...")
                        self.running = False
                        self._cleanup()
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
            
            # Force update the display
            pygame.display.flip()

    def _draw_game_end_screen(self):
        # Draw semi-transparent overlay first
        overlay = pygame.Surface((self.WIDTH, self.HEIGHT), pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 128))
        self.screen.blit(overlay, (0, 0))
        
        # Draw game end box
        box_width = 400
        box_height = 300
        box_x = (self.WIDTH - box_width) // 2
        box_y = (self.HEIGHT - box_height) // 2
        
        # Draw white background for the box
        pygame.draw.rect(self.screen, (255, 255, 255), 
                        (box_x, box_y, box_width, box_height))
        pygame.draw.rect(self.screen, (0, 0, 0), 
                        (box_x, box_y, box_width, box_height), 2)
        
        # Draw title
        title = self.title_font.render("Game Over!", True, (0, 0, 0))
        title_rect = title.get_rect(centerx=box_x + box_width//2, 
                                  y=box_y + 20)
        self.screen.blit(title, title_rect)
        
        # Draw winner
        if self.winner:
            winner_text = f"Winner: {self.winner}"
            winner_surface = self.font.render(winner_text, True, (0, 200, 0))
            winner_rect = winner_surface.get_rect(centerx=box_x + box_width//2,
                                                y=box_y + 70)
            self.screen.blit(winner_surface, winner_rect)
        
        # Draw final scores
        y_offset = box_y + 120
        for username, score in sorted(self.final_scores.items(), key=lambda x: x[1], reverse=True):
            score_text = f"{username}: {score} points"
            score_surface = self.font.render(score_text, True, (0, 0, 0))
            score_rect = score_surface.get_rect(centerx=box_x + box_width//2,
                                              y=y_offset)
            self.screen.blit(score_surface, score_rect)
            y_offset += 30
        
        # Draw instructions
        instructions = self.info_font.render("Press Q to quit", True, (100, 100, 100))
        instructions_rect = instructions.get_rect(centerx=box_x + box_width//2,
                                                y=box_y + box_height - 40)
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
                    score = 0 if (r, c) in self.blank_tiles else self.LETTER_VALUES.get(server_letter.upper(), 0)
                    score_font = pygame.font.SysFont(None, 16)
                    score_text = score_font.render(str(score), True, (80, 80, 80))
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
                    score = 0 if (r, c) in self.blank_tiles else self.LETTER_VALUES.get(buffer_letter.upper(), 0)
                    score_font = pygame.font.SysFont(None, 16)
                    score_text = score_font.render(str(score), True, (80, 80, 80))
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

        # Draw blank tile dialog if active
        if self.showing_blank_dialog:
            # Draw semi-transparent overlay
            overlay = pygame.Surface((self.WIDTH, self.HEIGHT), pygame.SRCALPHA)
            overlay.fill((0, 0, 0, 128))
            self.screen.blit(overlay, (0, 0))
            
            # Draw dialog box
            dialog_width = 300
            dialog_height = 150
            dialog_x = (self.WIDTH - dialog_width) // 2
            dialog_y = (self.HEIGHT - dialog_height) // 2
            
            pygame.draw.rect(self.screen, (255, 255, 255), 
                           (dialog_x, dialog_y, dialog_width, dialog_height))
            pygame.draw.rect(self.screen, (0, 0, 0), 
                           (dialog_x, dialog_y, dialog_width, dialog_height), 2)
            
            # Draw instructions
            text = self.font.render("Type a letter for the blank tile", True, (0, 0, 0))
            text_rect = text.get_rect(centerx=dialog_x + dialog_width//2, 
                                    y=dialog_y + 20)
            self.screen.blit(text, text_rect)
            
            text = self.info_font.render("(Press ESC to cancel)", True, (100, 100, 100))
            text_rect = text.get_rect(centerx=dialog_x + dialog_width//2, 
                                    y=dialog_y + 50)
            self.screen.blit(text, text_rect)

    def _draw_tile_rack(self):
        """Draw the player's tile rack."""
        rack_y = self.MARGIN + self.BOARD_SIZE * self.TILE_SIZE + 10
        
        # Draw rack background
        rack_bg = pygame.Rect(self.MARGIN - 5, rack_y - 5, 
                             len(self.tile_rack) * (self.TILE_SIZE + 5) + 5, 
                             self.TILE_SIZE + 10)
        pygame.draw.rect(self.screen, (220, 220, 220), rack_bg)
        pygame.draw.rect(self.screen, (100, 100, 100), rack_bg, 2)
        
        for i, letter in enumerate(self.tile_rack):
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
            score = 0 if letter == '?' else self.LETTER_VALUES.get(letter.upper(), 0)
            score_font = pygame.font.SysFont(None, 16)
            score_text = score_font.render(str(score), True, (80, 80, 80))
            score_rect = score_text.get_rect(bottomright=(x + self.TILE_SIZE - 3, rack_y + self.TILE_SIZE - 2))
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
        
        # Tiles remaining info
        tiles_text = f"Tiles in bag: {self.tiles_remaining}"
        tiles_surface = self.info_font.render(tiles_text, True, (0, 0, 0))
        self.screen.blit(tiles_surface, (self.MARGIN + 10, info_y + 5))
        
        # Rack count info
        rack_text = f"Your tiles: {len(self.tile_rack)}/7"
        rack_surface = self.info_font.render(rack_text, True, (0, 0, 0))
        self.screen.blit(rack_surface, (self.MARGIN + 10, info_y + 25))
        
        # Buffer info
        if self.letter_buffer:
            buffer_text = f"Placed letters: {len(self.letter_buffer)}"
            buffer_surface = self.info_font.render(buffer_text, True, (0, 0, 0))
            self.screen.blit(buffer_surface, (self.MARGIN + 250, info_y + 5))
        
        # Show waiting message if not started
        if not self.game_started:
            wait_text = "Waiting for all players to be ready..."
            wait_surface = self.info_font.render(wait_text, True, (200, 0, 0))
            self.screen.blit(wait_surface, (self.MARGIN + 250, info_y + 25))
        # Show "Your turn" message if it's the player's turn
        elif self.game_started and any(player.get("current_turn", False) for player in self.players):
            turn_text = "Your turn"
            turn_surface = self.info_font.render(turn_text, True, (0, 200, 0))  # Green color
            self.screen.blit(turn_surface, (self.MARGIN + 250, info_y + 25))

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
        return_text = self.button_font.render("Return", True, (0, 0, 0))
        return_rect = return_text.get_rect(center=self.return_button.center)
        self.screen.blit(return_text, return_rect)
        
        # Send button
        if self.exchange_mode:
            button_color = (100, 200, 100) if self.tiles_to_exchange else (150, 150, 150)
        else:
            button_color = (100, 200, 100) if self.letter_buffer and self.game_started else (150, 150, 150)
        pygame.draw.rect(self.screen, button_color, self.send_button)
        pygame.draw.rect(self.screen, (0, 0, 0), self.send_button, 2)
        send_text = self.button_font.render("Send", True, (0, 0, 0))
        send_rect = send_text.get_rect(center=self.send_button.center)
        self.screen.blit(send_text, send_rect)
        
        # Exchange button - always visible but grayed out if game not started
        if self.game_started:
            exchange_color = (255, 200, 200) if self.exchange_mode else (180, 180, 180)
        else:
            exchange_color = (150, 150, 150)  # Grayed out when game not started
        pygame.draw.rect(self.screen, exchange_color, self.exchange_button)
        pygame.draw.rect(self.screen, (0, 0, 0), self.exchange_button, 2)
        exchange_text = self.button_font.render("Exchange", True, (0, 0, 0))
        exchange_rect = exchange_text.get_rect(center=self.exchange_button.center)
        self.screen.blit(exchange_text, exchange_rect)
        
        # Ready button (only if game not started)
        if not self.game_started:
            ready_color = (100, 200, 255) if not self.ready else (180, 180, 180)
            pygame.draw.rect(self.screen, ready_color, self.ready_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.ready_button, 2)
            ready_text = self.button_font.render("Ready", True, (0, 0, 0))
            ready_rect = ready_text.get_rect(center=self.ready_button.center)
            self.screen.blit(ready_text, ready_rect)
        
        # Pass button (only if game started and player is ready)
        if self.game_started and self.ready and not self.game_ended:
            pass_color = (200, 200, 255)
            pygame.draw.rect(self.screen, pass_color, self.pass_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.pass_button, 2)
            pass_text = self.button_font.render("Pass", True, (0, 0, 0))
            pass_rect = pass_text.get_rect(center=self.pass_button.center)
            self.screen.blit(pass_text, pass_rect)
            
        # Shuffle button (only if game started and player is ready)
        if self.game_started and self.ready and not self.game_ended:
            shuffle_color = (200, 255, 200)  # Light green
            pygame.draw.rect(self.screen, shuffle_color, self.shuffle_button)
            pygame.draw.rect(self.screen, (0, 0, 0), self.shuffle_button, 2)
            shuffle_text = self.button_font.render("Shuffle", True, (0, 0, 0))
            shuffle_rect = shuffle_text.get_rect(center=self.shuffle_button.center)
            self.screen.blit(shuffle_text, shuffle_rect)

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
                text = f"{player['username']}: {status}"
            else:
                # After game start, show points and turn
                color = (0, 200, 0) if player["current_turn"] else (0, 0, 0)
                text = f"{player['username']}: {player['points']} pts"
                
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
                        # Normal tile selection
                        if self.selected_rack_index == i:
                            self.selected_rack_index = None
                        else:
                            self.selected_rack_index = i
                            self.selected_board_cell = None
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

    def _place_tile_in_buffer(self, row, col):
        """Place a selected tile from the rack into the client buffer."""
        if self.selected_rack_index is None:
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

    def _send_ready(self):
        """Send READY to server and mark as ready."""
        try:
            self.sock.sendall(b"READY\n")
            self.ready = True
        except Exception as e:
            print(f"Failed to send READY: {e}")

    def _handle_mouse_click(self, pos):
        """Handle mouse click events."""
        x, y = pos
        # Try button clicks first
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

    def _handle_button_click(self, x, y):
        """Handle clicks on buttons."""
        if not self.game_started:
            # Only allow ready button clicks before game starts
            if self.ready_button.collidepoint(x, y):
                self._send_ready()
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
        return False

    def _handle_mouse_motion(self, pos):
        """Handle mouse motion events."""
        if self.scroll_bar_dragging and self.scroll_bar_rect:
            x, y = pos
            log_y = self.MARGIN + 150
            # Calculate new scroll position based on mouse position
            relative_y = y - log_y - 30
            max_scroll = max(0, self.move_log_content_height - (self.move_log_height - 30))
            scroll_ratio = relative_y / (self.move_log_height - 30 - self.scroll_bar_height)
            new_scroll = int(scroll_ratio * max_scroll)
            self.move_log_scroll = max(0, min(max_scroll, new_scroll))

    def _handle_mouse_release(self):
        """Handle mouse release events."""
        self.scroll_bar_dragging = False

    def _handle_keydown(self, key):
        """Handle keyboard events."""
        # Always allow quitting with Q
        if key == pygame.K_q:
            # Quit with Q
            print("\nShutting down client...")
            self.running = False
            return
            
        if not self.game_started:
            self._set_error("Game has not started yet.")
            return
            
        # Handle blank tile letter selection
        if self.showing_blank_dialog:
            if pygame.K_a <= key <= pygame.K_z:
                letter = chr(key).upper()
                row, col = self.blank_pos
                self.letter_buffer[(row, col)] = letter
                self.blank_tiles.add((row, col))  # Mark this as a blank tile
                self.selected_rack_index = None  # Deselect after placing
                self.selected_board_cell = None  # Deselect after placing
                self.showing_blank_dialog = False
                self.blank_pos = None
            elif key == pygame.K_ESCAPE:
                self.showing_blank_dialog = False
                self.blank_pos = None
            return
            
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
        elif key == pygame.K_r:
            # Request rack update with 'R' key
            try:
                self.sock.sendall(b"GET_RACK")
            except Exception as e:
                self._set_error(f"Failed to request rack update: {e}")
        elif key == pygame.K_p:
            # Pass turn with 'P' key
            if not self.game_ended:
                try:
                    self.sock.sendall(b"PASS")
                except Exception as e:
                    self._set_error(f"Failed to pass turn: {e}")

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
                content_height += 20
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
        self.draw_board()
        try:
            while self.running:
                for event in pygame.event.get():
                    if event.type == pygame.QUIT:
                        print("[DEBUG] Received pygame.QUIT event")
                        self.running = False
                    elif event.type == pygame.MOUSEBUTTONDOWN:
                        if not self.game_ended:  # Only handle clicks if game hasn't ended
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
                        self._handle_keydown(event.key)
                # Auto-clear error message after 3 seconds
                if self.error_message and pygame.time.get_ticks() - self.error_time > 3000:
                    self.error_message = None
                self.draw_board()
                self.clock.tick(30)
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
        self.running = False
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
        clip_rect = pygame.Rect(log_x, log_y + 30, self.PLAYER_LIST_WIDTH - 20, self.move_log_height - 30)
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
                move_height += 20  # Pass move line
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
            num_surface = self.info_font.render(move_num, True, (100, 100, 100))
            if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                self.screen.blit(num_surface, (log_x + 5, y_offset))
            
            # Draw move content based on type
            if 'words' in move:  # Regular move
                player_text = f"{move['username']}: {move['total_points']} pts"
                player_surface = self.info_font.render(player_text, True, (0, 0, 0))
                if log_y + 30 <= y_offset <= log_y + self.move_log_height:
                    self.screen.blit(player_surface, (log_x + 25, y_offset))
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
                y_offset += 20
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
            letter_score = 0 if is_blank else self.LETTER_VALUES.get(letter.upper(), 0)
            square_type = self.special_tiles[row][col]
            
            # Check if this is a new tile (part of the current buffer)
            is_new_tile = (row, col) in self.letter_buffer
            
            if is_new_tile:  # Only apply letter multipliers to new non-blank tiles
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

def main():
    """Entry point for the application."""
    client = ScrabbleClient()
    client.run()


if __name__ == "__main__":
    main()