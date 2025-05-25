import socket
import threading
import json
import time
import sys
import random
from collections import defaultdict, Counter
import os
import msvcrt
import traceback


class ScrabbleServer:
    """A multi-client Scrabble game server."""
    
    # Class constants
    HOST = '0.0.0.0'  # Listen on all network interfaces
    PORT = 12345
    BOARD_SIZE = 15
    SOCKET_TIMEOUT = 1.0
    BUFFER_SIZE = 1024
    RACK_SIZE = 7
    
    # Standard Scrabble tile distribution
    TILE_DISTRIBUTION = {
        'A': 9, 'B': 2, 'C': 2, 'D': 4, 'E': 12, 'F': 2, 'G': 3, 'H': 2,
        'I': 9, 'J': 1, 'K': 1, 'L': 4, 'M': 2, 'N': 6, 'O': 8, 'P': 2,
        'Q': 1, 'R': 6, 'S': 4, 'T': 6, 'U': 4, 'V': 2, 'W': 2, 'X': 1,
        'Y': 2, 'Z': 1, '?': 2  # * represents blank tiles
    }

    # Standard Scrabble tile distribution
    # TILE_DISTRIBUTION = {
    #     'A': 0, 'B': 0, 'C': 0, 'D': 1, 'E': 0, 'F': 0, 'G': 0, 'H': 0,
    #     'I': 0, 'J': 0, 'K': 0, 'L': 0, 'M': 0, 'N': 0, 'O': 0, 'P': 0,
    #     'Q': 0, 'R': 0, 'S': 0, 'T': 0, 'U': 0, 'V': 0, 'W': 0, 'X': 0,
    #     'Y': 0, 'Z': 0, '?': 8  # * represents blank tiles
    # }

    # Add these class constants after the existing ones
    SPECIAL_SQUARES = {
        'DL': [(0,3), (0,11), (2,6), (2,8), (3,0), (3,7), (3,14),
               (6,2), (6,6), (6,8), (6,12), (7,3), (7,11),
               (8,2), (8,6), (8,8), (8,12), (11,0), (11,7), (11,14),
               (12,6), (12,8), (14,3), (14,11)],
        'TL': [(1,5), (1,9), (5,1), (5,5), (5,9), (5,13),
               (9,1), (9,5), (9,9), (9,13), (13,5), (13,9)],
        'DW': [(1,1), (2,2), (3,3), (4,4), (13,13), (12,12), (11,11), (10,10),
               (1,13), (2,12), (3,11), (4,10), (13,1), (12,2), (11,3), (10,4),
               (7,7)],
        'TW': [(0,0), (0,7), (0,14), (7,0), (7,14), (14,0), (14,7), (14,14)]
    }

    def __init__(self, host=None, port=None):
        """Initialize the Scrabble server."""
        self.host = host or self.HOST
        self.port = port or self.PORT
        
        # Game state
        self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
        self.clients = []
        self.client_lock = threading.Lock()
        
        # Player management
        self.client_usernames = {}  # {socket: username}
        self.player_racks = {}      # {username: [tiles]}
        self.player_counter = 1     # For auto-generating usernames
        
        # Tile bag
        self.tile_bag = self._initialize_tile_bag()
        self.bag_lock = threading.Lock()
        
        # Server socket
        self.server_socket = None
        self.running = False

        self.player_points = defaultdict(int)  # {username: points}
        self.current_turn = None
        self.turn_order = []
        self.turn_lock = threading.Lock()
        self.player_ready = {}  # {username: ready_status}
        self.handler_threads = []  # Track client handler threads
        self.game_started = False  # Track if game has started
        self.game_ended = False    # Track if game has ended
        self.consecutive_passes = 0  # Track consecutive passes
        self.last_move_was_pass = False  # Track if last move was a pass
        
        # Dictionary and move tracking
        self.dictionary = {}  # {word: definition}
        self.move_log = []    # List of moves for logging
        self.board_blanks = set()  # Track positions of blank tiles on the board
        self._load_dictionary()

    def _initialize_tile_bag(self):
        """Create tile bag with validation."""
        bag = []
        for letter, count in self.TILE_DISTRIBUTION.items():
            if count <= 0:
                continue
            bag.extend([letter] * count)
        
        if not bag:
            raise RuntimeError("Tile bag initialization failed - no tiles created")
            
        random.shuffle(bag)
        print(f"[TILE BAG] Initialized with {len(bag)} tiles: {bag[:10]}...")  # Log sample
        return bag

    def _draw_tiles(self, count):
        """Draw tiles from the bag (thread-safe)."""
        with self.bag_lock:
            drawn = []
            for _ in range(min(count, len(self.tile_bag))):
                if self.tile_bag:
                    drawn.append(self.tile_bag.pop())
            return drawn

    def _return_tiles_to_bag(self, tiles):
        """Return tiles to the bag and shuffle (thread-safe)."""
        with self.bag_lock:
            self.tile_bag.extend(tiles)
            random.shuffle(self.tile_bag)

    def _get_tiles_remaining(self):
        """Get remaining tile count (thread-safe)."""
        with self.bag_lock:
            return len(self.tile_bag)

    def _fill_rack(self, conn):
        """Fill a player's rack to RACK_SIZE."""
        username = self._get_username(conn)
        if not username:
            return []
            
        if not self.game_started:
            print(f"[RACK] {username} attempted to fill rack before game start")
            return []
            
        current_rack = self.player_racks.get(username, [])
        needed = self.RACK_SIZE - len(current_rack)
        if needed > 0:
            new_tiles = self._draw_tiles(needed)
            current_rack.extend(new_tiles)
            self.player_racks[username] = current_rack
            print(f"[RACK] {username} received {len(new_tiles)} tiles: {new_tiles}")
            return new_tiles
        return []

    def _setup_server_socket(self):
        """Create and configure the server socket."""
        try:
            self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.server_socket.bind((self.host, self.port))
            self.server_socket.listen()
            self.server_socket.settimeout(self.SOCKET_TIMEOUT)
            print(f"[SERVER STARTED] Listening on {self.host}:{self.port}")
            return True
        except Exception as e:
            print(f"[ERROR] Failed to setup server socket: {e}")
            return False

    def _broadcast_board(self):
        """Send current board state and blank positions to all clients."""
        board_data = {
            'type': 'board_update',
            'board': self.board,
            'blanks': list(self.board_blanks)
        }
        message = json.dumps(board_data).encode() + b'\n'
        with self.client_lock:
            clients_to_remove = []
            for client in self.clients[:]:
                try:
                    client.sendall(message)
                except Exception as e:
                    print(f"[ERROR] Failed to send to {self._get_username(client)}: {e}")
                    clients_to_remove.append(client)
            for client in clients_to_remove:
                self._remove_client(client)

    def _broadcast_player_list(self):
        """Send updated player list to all clients."""
        player_data = {
            "type": "players",
            "game_started": self.game_started,
            "players": [
                {
                    "username": username,
                    "points": self.player_points[username],
                    "current_turn": (username == self.current_turn),
                    "ready": self.player_ready.get(username, False)
                }
                for username in self.turn_order
            ]
        }
        self._broadcast_message(player_data)

    def _broadcast_message(self, data):
        """Broadcast JSON message to all clients."""
        message = json.dumps(data).encode() + b'\n'
        with self.client_lock:
            for conn in self.clients[:]:
                try:
                    conn.sendall(message)
                except:
                    self._remove_client(conn)

    def _send_rack_update(self, conn):
        """Send a player their current rack."""
        username = self._get_username(conn)
        if not username:
            return
        try:
            rack = self.player_racks.get(username, [])
            rack_data = {
                'type': 'rack_update',
                'rack': rack,
                'tiles_remaining': self._get_tiles_remaining(),
                'username': username
            }
            message = json.dumps(rack_data).encode() + b'\n'
            conn.sendall(message)
        except Exception as e:
            print(f"[ERROR] Failed to send rack update: {e}")

    def _add_client(self, conn):
        """Non-blocking client registration."""
        try:
            # Block new joins only if game is in progress (has players and is started)
            if self.game_started and self.turn_order:
                conn.sendall("ERROR:Game already in progress, cannot join\n".encode())
                conn.close()
                return
            conn.settimeout(5.0)
            username_msg = self._receive_line(conn)
            if not username_msg.startswith("USERNAME:"):
                conn.sendall("ERROR:Invalid username format\n".encode())
                conn.close()
                return
            username = username_msg[9:].strip()
            
            # Check if username is currently in use by an active connection
            with self.client_lock:
                if username in self.client_usernames.values():
                    conn.sendall("ERROR:Username already in use\n".encode())
                    conn.close()
                    return
                    
                self.clients.append(conn)
                self.client_usernames[conn.fileno()] = username
                if username not in self.player_racks:
                    self.player_racks[username] = []
                if username not in self.player_points:
                    self.player_points[username] = 0
                # --- Turn system initialization ---
                if username not in self.turn_order:
                    self.turn_order.append(username)
                if self.current_turn is None:
                    self.current_turn = self.turn_order[0]
                # --- End turn system initialization ---
                conn.sendall("OK:Username accepted\n".encode())
            self._broadcast_player_list()
        except socket.timeout:
            print(f"Client connection timed out during registration")
            conn.close()
        except Exception as e:
            print(f"Client registration failed: {str(e)}")
            conn.close()

    def _receive_line(self, conn):
        """Helper to read a complete line."""
        buffer = []
        while True:
            chunk = conn.recv(1).decode()
            if chunk == '\n' or not chunk:
                break
            buffer.append(chunk)
        return ''.join(buffer)

    def _remove_client(self, conn):
        """Remove client and update all relevant state."""
        username = self._get_username(conn)
        try:
            with self.client_lock:
                if conn in self.clients:
                    self.clients.remove(conn)
                fileno = conn.fileno()
                if fileno in self.client_usernames:
                    del self.client_usernames[fileno]
                # Remove from all game state
                if username:
                    if username in self.player_racks:
                        del self.player_racks[username]
                    if username in self.player_points:
                        del self.player_points[username]
                    if username in self.player_ready:
                        del self.player_ready[username]
                    if username in self.turn_order:
                        idx = self.turn_order.index(username)
                        self.turn_order.remove(username)
                        # If it was their turn, advance turn
                        if self.current_turn == username:
                            if self.turn_order:
                                self.current_turn = self.turn_order[idx % len(self.turn_order)]
                            else:
                                self.current_turn = None
            try:
                conn.close()
            except:
                pass
            print(f"[DISCONNECTED] {username if username else conn} (fully removed)")
            # If all players left, reset game state
            if not self.turn_order:
                self.game_started = False
                self.game_ended = False
                self.current_turn = None
                self.player_racks.clear()
                self.player_points.clear()
                self.player_ready.clear()
                # Reset the tile bag
                self.tile_bag = self._initialize_tile_bag()
                # Reset the board
                self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
                # Clear the move log
                self.move_log.clear()
                self.board_blanks.clear()
                print("[SERVER] All players left. Game state reset.")
            else:
                # If game hasn't started, check if all remaining are ready
                if not self.game_started and all(self.player_ready.get(u, False) for u in self.turn_order):
                    self.game_started = True
                    self._broadcast_message({"type": "game_start"})
            self._broadcast_player_list()
            self._broadcast_board()
        except Exception as e:
            print(f"[ERROR] Error removing client: {e}")

    def _send_initial_data(self, conn):
        """Send board and rack to new/reconnected player."""
        username = self._get_username(conn)
        if not username:
            return
        try:
            initial_data = json.dumps(self.board).encode() + b'\n'
            conn.sendall(initial_data)
            self._send_rack_update(conn)
        except Exception as e:
            print(f"[ERROR] Failed to send initial data to {username}: {e}")

    def _parse_move(self, data):
        """Validate and parse move data."""
        try:
            # If the data contains a blank position marker, remove it
            if '|' in data:
                data = data.split('|')[0]
                
            parts = data.split(',')
            if len(parts) != 3:
                raise ValueError("Move must have exactly 3 parts: row,col,char")
            
            row, col, char = parts
            row, col = int(row), int(col)
            
            if not (0 <= row < self.BOARD_SIZE and 0 <= col < self.BOARD_SIZE):
                raise ValueError(f"Position ({row},{col}) is out of bounds")
            
            if len(char) != 1:
                raise ValueError("Character must be exactly one letter")
            
            return row, col, char.upper()
        except Exception as e:
            raise ValueError(f"Invalid move format: {e}")

    def _validate_tiles_available(self, conn, tiles):
        """Validate that the player has all the required tiles."""
        username = self._get_username(conn)
        if not username:
            raise ValueError("Not logged in")
        
        rack = self.player_racks[username]
        rack_copy = rack.copy()  # Make a copy to track available tiles
        
        # Check each tile in the move
        for tile in tiles:
            if tile == '?':  # Handle blank tiles
                if '?' not in rack_copy:
                    raise ValueError(f"Not enough blank tiles. Need 1, have 0")
                rack_copy.remove('?')
            else:
                if tile not in rack_copy:
                    # If we don't have the letter, check if we have a blank
                    if '?' in rack_copy:
                        rack_copy.remove('?')  # Use a blank tile
                    else:
                        raise ValueError(f"Not enough {tile} tiles. Need 1, have 0")
                else:
                    rack_copy.remove(tile)  # Use the regular tile

    def _remove_tiles_from_rack(self, conn, tiles_used):
        """Remove used tiles from player's rack."""
        username = self._get_username(conn)
        if not username or username not in self.player_racks:
            return
        rack = self.player_racks[username]
        for tile in tiles_used:
            if tile in rack:
                rack.remove(tile)
        print(f"[RACK] {username} used tiles: {tiles_used}")

    def _get_square_type(self, row, col):
        """Get the type of special square at the given position."""
        for square_type, positions in self.SPECIAL_SQUARES.items():
            if (row, col) in positions:
                return square_type
        return None

    def _calculate_word_score(self, moves, blank_positions=None):
        """Calculate the score for a word, including special squares and bingo bonus."""
        total_score = 0
        tiles_used = len(moves)
        
        # Get all words created by this play
        words = self._get_all_words(moves)
        print(f"[DEBUG] Words created: {words}")  # Debug log
        
        # Create a temporary board with the moves
        temp_board = [row[:] for row in self.board]
        temp_blanks = self.board_blanks.copy()  # Copy current blank positions
        
        # Create a set of positions that were just played
        new_positions = {(row, col) for row, col, _ in moves}
        
        # Add client's blank positions to temp_blanks
        if blank_positions:
            temp_blanks.update(blank_positions)
            print(f"[DEBUG] Added client blank positions: {blank_positions}")  # Debug log
        
        # Add new moves to temp board and track new blank positions
        for row, col, char in moves:
            temp_board[row][col] = char
            # If this position was in the original blank_positions, add it to temp_blanks
            if (row, col) in self.board_blanks:
                temp_blanks.add((row, col))
        
        # Calculate score for each word
        for word in words:
            word_score = 0
            word_mult = 1
            word_positions = []
            
            # Find the word in the temporary board
            found = False
            # Check horizontal
            for row in range(self.BOARD_SIZE):
                for col in range(self.BOARD_SIZE):
                    if temp_board[row][col] != '':
                        # Get the word at this position
                        current_word = []
                        positions = []
                        # Look left
                        c = col
                        while c >= 0 and temp_board[row][c] != '':
                            current_word.insert(0, temp_board[row][c])
                            positions.insert(0, (row, c))
                            c -= 1
                        # Look right
                        c = col + 1
                        while c < self.BOARD_SIZE and temp_board[row][c] != '':
                            current_word.append(temp_board[row][c])
                            positions.append((row, c))
                            c += 1
                        if ''.join(current_word) == word:
                            word_positions = positions
                            found = True
                            break
                if found:
                    break
            
            # If not found horizontally, check vertical
            if not found:
                for col in range(self.BOARD_SIZE):
                    for row in range(self.BOARD_SIZE):
                        if temp_board[row][col] != '':
                            # Get the word at this position
                            current_word = []
                            positions = []
                            # Look up
                            r = row
                            while r >= 0 and temp_board[r][col] != '':
                                current_word.insert(0, temp_board[r][col])
                                positions.insert(0, (r, col))
                                r -= 1
                            # Look down
                            r = row + 1
                            while r < self.BOARD_SIZE and temp_board[r][col] != '':
                                current_word.append(temp_board[r][col])
                                positions.append((r, col))
                                r += 1
                            if ''.join(current_word) == word:
                                word_positions = positions
                                found = True
                                break
                    if found:
                        break
            
            print(f"[DEBUG] Word '{word}' positions: {word_positions}")  # Debug log
            
            # Skip words that don't contain any newly played tiles
            if not any(pos in new_positions for pos in word_positions):
                print(f"[DEBUG] Skipping word '{word}' as it contains no new tiles")
                continue
            
            # Check if this is the primary word (contains all new moves)
            is_primary_word = all(any(r == row and c == col for row, col in word_positions) for r, c, _ in moves)
            
            # Calculate score for this word
            for row, col in word_positions:
                letter = temp_board[row][col]  # Use temp_board to get the correct letter
                # Check if this is a blank tile
                is_blank = (row, col) in temp_blanks
                # Always score 0 for blank tiles
                letter_score = 0 if is_blank else self._get_letter_value(letter)
                square_type = self._get_square_type(row, col)
                
                # Check if this is a new tile (part of the current move)
                is_new_tile = (row, col) in new_positions
                
                print(f"[DEBUG] Letter {letter} at ({row},{col}): base={letter_score}, square={square_type}, new={is_new_tile}, is_blank={is_blank}")  # Debug log
                
                if is_new_tile:
                    # Apply letter multipliers only to new tiles
                    if square_type == 'DL':
                        letter_score *= 2
                    elif square_type == 'TL':
                        letter_score *= 3
                    # Apply word multipliers to all tiles
                    if square_type == 'DW':
                        word_mult *= 2
                    elif square_type == 'TW':
                        word_mult *= 3
                
                word_score += letter_score
                print(f"[DEBUG] Running word score: {word_score}")  # Debug log
            
            # Apply word multiplier
            word_score *= word_mult
            print(f"[DEBUG] Final word score for '{word}': {word_score} (multiplier: {word_mult})")  # Debug log
            total_score += word_score
            
            # Add bingo bonus (50 points) only for primary words that use all 7 tiles
            if is_primary_word and tiles_used == 7:
                total_score += 50
                print("[DEBUG] Added bingo bonus of 50 points")  # Debug log
        
        print(f"[DEBUG] Total score for play: {total_score}")  # Debug log
        return total_score

    def _process_batch_move(self, conn, batch_data):
        """Process multiple moves in one batch, enforcing turn order."""
        username = self._get_username(conn)
        # Validate it's the player's turn
        if not username or username != self.current_turn:
            raise ValueError("Not your turn")
            
        # Split moves and blank positions
        if '|' in batch_data:
            moves_str, blank_positions_str = batch_data.split('|')
            blank_positions = set()
            # Split the blank positions string into pairs of coordinates
            pos_pairs = blank_positions_str.split(',')
            for i in range(0, len(pos_pairs), 2):
                if i + 1 < len(pos_pairs):
                    r, c = int(pos_pairs[i]), int(pos_pairs[i + 1])
                    blank_positions.add((r, c))
                    print(f"[DEBUG] Added blank position: ({r}, {c})")  # Debug log
        else:
            moves_str = batch_data
            blank_positions = set()
            
        moves = moves_str.split(';')
        processed_moves = []
        tiles_used = []
        
        # First pass: collect all moves and tiles
        for move_str in moves:
            move_str = move_str.strip()
            if not move_str:
                continue
            row, col, char = self._parse_move(move_str)
            if self.board[row][col] != '':
                raise ValueError(f"Position ({row},{col}) is already occupied")
            for prev_row, prev_col, _ in processed_moves:
                if row == prev_row and col == prev_col:
                    raise ValueError(f"Duplicate position ({row},{col}) in batch")
            processed_moves.append((row, col, char))
            tiles_used.append(char)  # Add the tile to be used
        
        # Validate tiles are available
        self._validate_tiles_available(conn, tiles_used)
        
        # Validate the play
        is_valid, message = self._validate_play(processed_moves)
        if not is_valid:
            raise ValueError(message)
        
        # Calculate score for the word
        word_score = self._calculate_word_score(processed_moves, blank_positions)
        
        # Remove tiles from rack
        rack = self.player_racks[username]
        for i, char in enumerate(tiles_used):
            row, col, _ = processed_moves[i]  # Get the position for this tile
            if (row, col) in blank_positions:  # If this position was marked as a blank
                rack.remove('?')  # Remove a blank tile
            else:
                rack.remove(char)  # Remove the regular tile
        
        # Apply all valid moves and update blank positions
        for row, col, char in processed_moves:
            self.board[row][col] = char
            # Only mark as blank if the position was in the blank_positions set
            if (row, col) in blank_positions:
                self.board_blanks.add((row, col))
                print(f"[DEBUG] Marking position ({row}, {col}) as blank")
        
        # Get all words created by this play
        words = self._get_all_words(processed_moves)
        
        # Log the move
        self._log_move(username, words, word_score, processed_moves)
        
        # Update player's score BEFORE checking for game end
        self.player_points[username] += word_score
        
        # Fill rack
        new_tiles = self._fill_rack(conn)
        
        # Reset consecutive passes since a valid move was made
        self.consecutive_passes = 0
        self.last_move_was_pass = False
        
        print(f"[BATCH] {username} placed {len(processed_moves)} tiles for {word_score} points")
        
        # Switch turns after a valid batch move
        with self.turn_lock:
            current_idx = self.turn_order.index(self.current_turn)
            next_idx = (current_idx + 1) % len(self.turn_order)
            self.current_turn = self.turn_order[next_idx]
        
        # Broadcast updates
        self._broadcast_board()
        self._broadcast_player_list()
        self._broadcast_move_log()  # Ensure move log is broadcast
        
        # Check for game end - only end if player used all tiles AND bag is empty
        if not self.player_racks[username] and self._get_tiles_remaining() == 0:
            self._end_game()
            return

    def _handle_pass(self, conn):
        """Handle a player passing their turn."""
        username = self._get_username(conn)
        if not username or username != self.current_turn:
            raise ValueError("Not your turn")
            
        if self.last_move_was_pass:
            self.consecutive_passes += 1
            # End game after one pass in a one-player game, or after all players pass in multi-player
            if len(self.turn_order) == 1 or self.consecutive_passes >= len(self.turn_order):
                self._end_game()
                return
        else:
            self.consecutive_passes = 1
            self.last_move_was_pass = True
            
        # Log the pass
        pass_info = {
            "username": username,
            "type": "pass"
        }
        self.move_log.append(pass_info)
        
        # Switch turns
        with self.turn_lock:
            current_idx = self.turn_order.index(self.current_turn)
            next_idx = (current_idx + 1) % len(self.turn_order)
            self.current_turn = self.turn_order[next_idx]
            
        # Broadcast updates
        self._broadcast_player_list()
        self._broadcast_move_log()

    def _end_game(self):
        """Handle end of game procedures."""
        if self.game_ended:
            print("[DEBUG] Game already ended, skipping end game procedure")
            return
            
        print("[DEBUG] Starting end game procedure")
        self.game_ended = True
        print("[GAME] Game has ended")
        
        try:
            # Calculate final scores
            final_scores = {}
            print("[DEBUG] Calculating final scores")
            for username in self.turn_order:
                print(f"[DEBUG] Processing player: {username}")
                # Get remaining tiles
                remaining_tiles = self.player_racks[username]
                print(f"[DEBUG] Remaining tiles for {username}: {remaining_tiles}")
                # Calculate penalty
                penalty = sum(self._get_letter_value(tile) for tile in remaining_tiles)
                print(f"[DEBUG] Penalty for {username}: {penalty}")
                # Subtract penalty from score
                final_score = self.player_points[username] - penalty
                final_scores[username] = final_score
                print(f"[DEBUG] Final score for {username}: {final_score}")
                
                # Update player's score
                self.player_points[username] = final_score
                
                # Return tiles to bag
                self._return_tiles_to_bag(remaining_tiles)
                self.player_racks[username] = []
            
            print(f"[DEBUG] Final scores calculated: {final_scores}")
            
            # Log final scores
            final_score_info = {
                "type": "game_end",
                "scores": final_scores
            }
            self.move_log.append(final_score_info)
            print("[DEBUG] Added final scores to move log")
            
            # Broadcast final state
            print("[DEBUG] Broadcasting final state")
            self._broadcast_player_list()
            self._broadcast_move_log()
            
            # Send game end message to all clients
            end_message = {
                "type": "game_end",
                "scores": final_scores
            }
            print(f"[DEBUG] Sending game end message: {end_message}")
            self._broadcast_message(end_message)
            print("[DEBUG] Game end message broadcast complete")
            
        except Exception as e:
            print(f"[ERROR] Error in end game procedure: {e}")
            traceback.print_exc()

    def _handle_draw_request(self, conn, count_str):
        """Handle tile drawing request."""
        try:
            username = self._get_username(conn)
            if not username:
                raise ValueError("Player not identified")
                
            if not self.game_started:
                raise ValueError("Game has not started yet. Wait for all players to be ready.")
                
            count = int(count_str)
            if not (1 <= count <= 7):
                raise ValueError("Can only draw 1-7 tiles at a time")
            
            current_rack = self.player_racks.get(username, [])
            if len(current_rack) + count > self.RACK_SIZE:
                raise ValueError(f"Cannot exceed rack size of {self.RACK_SIZE}")
            
            new_tiles = self._draw_tiles(count)
            current_rack.extend(new_tiles)
            self._send_rack_update(conn)
            print(f"[DRAW] {username} drew {len(new_tiles)} tiles")
            
        except ValueError as e:
            error_msg = f"Draw Error: {e}\n"
            conn.sendall(error_msg.encode())

    def _handle_exchange_request(self, conn, tiles_str):
        """Handle tile exchange request."""
        try:
            # Validate it's the player's turn
            username = self._get_username(conn)
            if not username or username != self.current_turn:
                raise ValueError("Not your turn")
            
            # Parse tiles to exchange
            tiles_to_exchange = tiles_str.split(',')
            if not tiles_to_exchange:
                raise ValueError("No tiles specified for exchange")
            
            # Validate tiles are in player's rack
            rack = self.player_racks.get(username, [])
            rack_counter = Counter(rack)
            exchange_counter = Counter(tiles_to_exchange)
            
            for tile, count in exchange_counter.items():
                if rack_counter[tile] < count:
                    raise ValueError(f"Not enough '{tile}' tiles to exchange")
            
            # Check if there are enough tiles in the bag
            if len(tiles_to_exchange) > self._get_tiles_remaining():
                raise ValueError("Not enough tiles in bag for exchange")
            
            # Remove tiles from rack
            for tile in tiles_to_exchange:
                rack.remove(tile)
            
            # Draw new tiles
            new_tiles = self._draw_tiles(len(tiles_to_exchange))
            
            # Return old tiles to bag
            self._return_tiles_to_bag(tiles_to_exchange)
            
            # Add new tiles to rack
            rack.extend(new_tiles)
            
            # Update rack
            self.player_racks[username] = rack
            
            # Log the exchange move
            exchange_info = {
                "username": username,
                "type": "exchange"
            }
            self.move_log.append(exchange_info)
            
            # Switch turns
            with self.turn_lock:
                current_idx = self.turn_order.index(self.current_turn)
                next_idx = (current_idx + 1) % len(self.turn_order)
                self.current_turn = self.turn_order[next_idx]
            
            # Send updated rack and broadcast player list
            self._send_rack_update(conn)
            self._broadcast_player_list()
            self._broadcast_move_log()  # Broadcast the updated move log
            
            print(f"[EXCHANGE] {username} exchanged {len(tiles_to_exchange)} tiles")
            
        except ValueError as e:
            error_msg = f"Exchange Error: {e}\n"
            conn.sendall(error_msg.encode())

    def _handle_client(self, conn, addr):
        """Main client handler loop."""
        print(f"[CONNECTION] From {addr}")
        username = None
        try:
            self._add_client(conn)
            fileno = conn.fileno()
            username = self.client_usernames.get(fileno)
            self._send_initial_data(conn)
            conn.settimeout(1.0)
            while self.running:
                try:
                    data = conn.recv(1024).decode().strip()
                    if not data:
                        print(f"[DISCONNECT] Client {username or addr} disconnected (no data)")
                        break
                    try:
                        if data == "DISCONNECT":
                            print(f"[DISCONNECT] Client {username or addr} requested disconnect")
                            break
                        elif data == "READY":
                            self.player_ready[username] = True
                            self._broadcast_player_list()
                            if all(self.player_ready.get(u, False) for u in self.turn_order):
                                self.game_started = True
                                # Fill racks for all players when game starts
                                with self.client_lock:
                                    for client in self.clients:
                                        self._fill_rack(client)
                                self._broadcast_message({"type": "game_start"})
                        # Block all other actions before game start
                        elif not self.game_started:
                            if data == 'GET_RACK':
                                self._send_rack_update(conn)
                            else:
                                conn.sendall("ERROR:Game has not started yet. Wait for all players to be ready.\n".encode())
                        elif data == "PASS":
                            self._handle_pass(conn)
                        elif data.startswith('DRAW:'):
                            self._handle_draw_request(conn, data[5:])
                        elif data.startswith('EXCHANGE:'):
                            self._handle_exchange_request(conn, data[9:])
                        elif data == 'GET_RACK':
                            self._send_rack_update(conn)
                        elif ';' in data:
                            self._process_batch_move(conn, data)
                            self._broadcast_board()
                            self._send_rack_update(conn)
                        else:
                            # For single moves, just pass the data directly to _process_batch_move
                            self._process_batch_move(conn, data)
                            self._broadcast_board()
                            self._send_rack_update(conn)
                    except ValueError as e:
                        error_msg = f"Error: {e}\n"
                        conn.sendall(error_msg.encode())
                except socket.timeout:
                    continue
                except ConnectionResetError:
                    print(f"[DISCONNECT] Client {username or addr} disconnected (connection reset)")
                    break
                except Exception as e:
                    print(f"[ERROR] Client handler error for {username or addr}: {e}")
                    break
        except Exception as e:
            print(f"[ERROR] Client {addr} error: {e}")
            traceback.print_exc()
        finally:
            print(f"[DISCONNECT] Removing client {username or addr}")
            self._remove_client(conn)

    def _accept_clients(self):
        """Accept incoming client connections with proper interrupt handling and ESC key support."""
        while self.running:
            try:
                if msvcrt.kbhit():
                    key = msvcrt.getch()
                    if key == b'\x1b':
                        print("\n[SERVER] ESC key pressed, shutting down...")
                        self.running = False
                        break
                try:
                    conn, addr = self.server_socket.accept()
                    client_thread = threading.Thread(
                        target=self._handle_client, 
                        args=(conn, addr),
                        daemon=True
                    )
                    client_thread.start()
                    self.handler_threads.append(client_thread)
                except socket.timeout:
                    continue
                except OSError:
                    if not self.running:
                        break
                    raise
            except KeyboardInterrupt:
                print("\n[SERVER] Keyboard interrupt received in accept loop")
                self.running = False
                break
            except Exception as e:
                if self.running:
                    print(f"[ERROR] Accept error: {e}")
                break

    def start(self):
        """Start the server with proper interrupt handling."""
        if not self._setup_server_socket():
            return False
        
        self.running = True
        print("[SERVER] Ready for connections")
        
        try:
            self._accept_clients()
        except KeyboardInterrupt:
            pass  # Let the finally block handle shutdown
        except Exception as e:
            print(f"[SERVER] Error: {e}")
        finally:
            if self.running:  # Only stop if not already stopped
                self.stop()
        
        return True

    def stop(self):
        """Proper shutdown procedure."""
        if not self.running:
            return
        print("[SERVER] Shutting down...")
        self.running = False
        with self.client_lock:
            for client in self.clients[:]:
                try:
                    client.sendall("ERROR:Server shutting down\n".encode())
                except:
                    pass
        if self.server_socket:
            try:
                self.server_socket.close()
            except:
                pass
        with self.client_lock:
            for client in self.clients[:]:
                try:
                    client.close()
                except:
                    pass
            self.clients.clear()
            self.client_usernames.clear()
            self.player_racks.clear()
            self.player_points.clear()
            self.player_ready.clear()
            self.turn_order.clear()
            self.current_turn = None
            # Reset the tile bag
            self.tile_bag = self._initialize_tile_bag()
            # Reset the board
            self.board = [['' for _ in range(self.BOARD_SIZE)] for _ in range(self.BOARD_SIZE)]
            # Clear the move log
            self.move_log.clear()
            self.board_blanks.clear()
        # Wait for all handler threads to finish
        for t in self.handler_threads:
            t.join(timeout=2)
        print("[SERVER] Stopped")

    # Additional utility methods
    def print_board(self):
        """Print the current board state."""
        print("\nCurrent Board:")
        print("  " + " ".join(f"{i:2d}" for i in range(self.BOARD_SIZE)))
        for i, row in enumerate(self.board):
            row_str = " ".join(f"{cell:2s}" if cell else " ." for cell in row)
            print(f"{i:2d} {row_str}")
        print()

    def print_status(self):
        """Print server status."""
        print(f"\n[STATUS] Connected players: {len(self.player_racks)}")
        print(f"[STATUS] Tiles remaining: {self._get_tiles_remaining()}")
        print(f"[STATUS] Active racks: { {k: len(v) for k, v in self.player_racks.items()} }")

    def _get_username(self, conn):
        fileno = conn.fileno()
        return self.client_usernames.get(fileno)

    def _get_letter_value(self, char):
        """Return the standard Scrabble letter value for a given character."""
        values = {
            'A': 1, 'B': 3, 'C': 3, 'D': 2, 'E': 1, 'F': 4, 'G': 2, 'H': 4,
            'I': 1, 'J': 8, 'K': 5, 'L': 1, 'M': 3, 'N': 1, 'O': 1, 'P': 3,
            'Q': 10, 'R': 1, 'S': 1, 'T': 1, 'U': 1, 'V': 4, 'W': 4, 'X': 8,
            'Y': 4, 'Z': 10, '?': 0
        }
        return values.get(char.upper(), 0)

    def _load_dictionary(self):
        """Load the Scrabble dictionary with definitions."""
        try:
            with open('assets/dictionary/words_with_definitions.txt', 'r', encoding='utf-8') as f:
                # Skip the header line
                next(f)
                for line in f:
                    # Split on tab and take both word and definition
                    parts = line.strip().split('\t')
                    if len(parts) >= 2:
                        word = parts[0].strip().upper()
                        definition = parts[1].strip()
                        self.dictionary[word] = definition
            print(f"[DICTIONARY] Loaded {len(self.dictionary)} words with definitions")
        except Exception as e:
            print(f"[ERROR] Failed to load dictionary: {e}")
            sys.exit(1)

    def _get_word_definition(self, word):
        """Get the definition of a word from the dictionary."""
        return self.dictionary.get(word, "Definition not found")

    def _log_move(self, username, words, points, positions):
        """Log a move with words played, points, and positions."""
        move_info = {
            "username": username,
            "words": [],
            "total_points": points
        }
        
        # Create a temporary board with the moves
        temp_board = [row[:] for row in self.board]
        for row, col, char in positions:
            temp_board[row][col] = char
        
        # Process each word and its positions
        for word in words:
            # Get all positions for this word
            word_positions_list = self._current_word_positions.get(word, [])
            for word_positions in word_positions_list:
                word_info = {
                    "word": word,
                    "definition": self._get_word_definition(word),
                    "positions": []  # List of (row, col, letter, square_type) tuples
                }
                
                # Add all positions with their square types
                for r, c in word_positions:
                    square_type = self._get_square_type(r, c)
                    word_info["positions"].append((r, c, temp_board[r][c], square_type))
                
                move_info["words"].append(word_info)
        
        # Clear the stored positions
        self._current_word_positions = {}
        
        self.move_log.append(move_info)
        # Broadcast move log update
        self._broadcast_move_log()

    def _broadcast_move_log(self):
        """Broadcast the move log to all clients."""
        move_log_data = {
            "type": "move_log",
            "moves": self.move_log
        }
        message = json.dumps(move_log_data).encode() + b'\n'
        with self.client_lock:
            for conn in self.clients[:]:
                try:
                    conn.sendall(message)
                except:
                    self._remove_client(conn)

    def _get_word_at_position(self, row, col, horizontal=True):
        """Get the word at a given position, including any extensions."""
        word = []
        if horizontal:
            # Look left
            c = col
            while c >= 0 and self.board[row][c] != '':
                word.insert(0, self.board[row][c])
                c -= 1
            # Look right
            c = col + 1
            while c < self.BOARD_SIZE and self.board[row][c] != '':
                word.append(self.board[row][c])
                c += 1
        else:
            # Look up
            r = row
            while r >= 0 and self.board[r][col] != '':
                word.insert(0, self.board[r][col])
                r -= 1
            # Look down
            r = row + 1
            while r < self.BOARD_SIZE and self.board[r][col] != '':
                word.append(self.board[r][col])
                r += 1
        return ''.join(word) if len(word) > 1 else ''

    def _get_all_words(self, moves):
        """Get all words created by a set of moves."""
        words = {}  # Track each instance of a word: {word: count}
        word_positions = {}  # Track positions for each word: {word: [(positions), ...]}
        
        # Create a temporary board with the moves
        temp_board = [row[:] for row in self.board]
        for row, col, char in moves:
            temp_board[row][col] = char
        
        # Create a set of positions that were just played
        new_positions = {(row, col) for row, col, _ in moves}
        
        # Check horizontal words
        for row, col, char in moves:
            # Get the word at this position
            word = []
            positions = []
            # Look left
            c = col
            while c >= 0 and temp_board[row][c] != '':
                word.insert(0, temp_board[row][c])
                positions.insert(0, (row, c))
                c -= 1
            # Look right
            c = col + 1
            while c < self.BOARD_SIZE and temp_board[row][c] != '':
                word.append(temp_board[row][c])
                positions.append((row, c))
                c += 1
            # Only add the word if it's at least 2 letters long AND contains at least one new position
            if len(word) >= 2 and any(pos in new_positions for pos in positions):
                word_str = ''.join(word)
                positions_tuple = tuple(positions)
                # Only count as duplicate if positions are different
                if word_str not in word_positions or positions_tuple not in word_positions[word_str]:
                    words[word_str] = words.get(word_str, 0) + 1
                    if word_str not in word_positions:
                        word_positions[word_str] = []
                    word_positions[word_str].append(positions_tuple)
        
        # Check vertical words
        for row, col, char in moves:
            # Get the word at this position
            word = []
            positions = []
            # Look up
            r = row
            while r >= 0 and temp_board[r][col] != '':
                word.insert(0, temp_board[r][col])
                positions.insert(0, (r, col))
                r -= 1
            # Look down
            r = row + 1
            while r < self.BOARD_SIZE and temp_board[r][col] != '':
                word.append(temp_board[r][col])
                positions.append((r, col))
                r += 1
            # Only add the word if it's at least 2 letters long AND contains at least one new position
            if len(word) >= 2 and any(pos in new_positions for pos in positions):
                word_str = ''.join(word)
                positions_tuple = tuple(positions)
                # Only count as duplicate if positions are different
                if word_str not in word_positions or positions_tuple not in word_positions[word_str]:
                    words[word_str] = words.get(word_str, 0) + 1
                    if word_str not in word_positions:
                        word_positions[word_str] = []
                    word_positions[word_str].append(positions_tuple)
        
        print(f"[DEBUG] Found words: {words}")  # Debug log
        print(f"[DEBUG] Word positions: {word_positions}")  # Debug log
        
        # Store the positions in the class for _log_move to use
        self._current_word_positions = word_positions
        
        # Return just the set of words for backward compatibility
        return set(words.keys())

    def _validate_play(self, moves):
        """Validate a play, checking all created words and connections."""
        if not moves:
            return False, "No moves provided"
        
        # Check if this is the first play
        is_first_play = all(self.board[r][c] == '' for r in range(self.BOARD_SIZE) for c in range(self.BOARD_SIZE))
        
        # Create a temporary board with the moves
        temp_board = [row[:] for row in self.board]
        for row, col, char in moves:
            temp_board[row][col] = char
        
        # Validate that all new tiles are in a straight line
        if not self._are_tiles_in_line(moves):
            return False, "All new tiles must be placed in a straight line (horizontal or vertical)"
        
        # Get all words created by this play
        words = self._get_all_words(moves)
        
        # If no words were created, the play is invalid
        if not words:
            return False, "Play must create at least one word"
        
        # Validate all words
        invalid_words = [word for word in words if word not in self.dictionary]
        if invalid_words:
            return False, f"Invalid words: {', '.join(invalid_words)}"
        
        # Check if play connects to existing words (unless it's the first play)
        if not is_first_play:
            connected = False
            for row, col, _ in moves:
                # Check if this move connects to any existing tiles
                for dr, dc in [(0, 1), (1, 0), (0, -1), (-1, 0)]:
                    nr, nc = row + dr, col + dc
                    if (0 <= nr < self.BOARD_SIZE and 0 <= nc < self.BOARD_SIZE and 
                        self.board[nr][nc] != ''):
                        connected = True
                        break
                if connected:
                    break
            if not connected:
                return False, "Play must connect to at least one existing tile"
        else:
            # For first play, check if it goes through the center star
            goes_through_center = False
            for row, col, _ in moves:
                if row == 7 and col == 7:  # Center star position
                    goes_through_center = True
                    break
            if not goes_through_center:
                return False, "First word must go through the center star"
        
        return True, "Valid play"

    def _are_tiles_in_line(self, moves):
        """Check if all new tiles are placed in a straight line (horizontal or vertical)."""
        if not moves:
            return True
        
        # Get all positions
        positions = [(row, col) for row, col, _ in moves]
        if not positions:
            return True
        
        # Check if all positions are in the same row
        same_row = all(pos[0] == positions[0][0] for pos in positions)
        if same_row:
            return True
        
        # Check if all positions are in the same column
        same_col = all(pos[1] == positions[0][1] for pos in positions)
        if same_col:
            return True
        
        # If neither same row nor same column, it's not a straight line
        return False


def main():
    """Entry point for the server."""
    server = ScrabbleServer()
    try:
        server.start()
    except KeyboardInterrupt:
        print("\nKeyboard interrupt received, initiating shutdown...")
    except Exception as e:
        print(f"Fatal error: {e}")
    finally:
        if server.running:
            server.stop()
        print("Server shutdown complete")
        os._exit(0)


if __name__ == "__main__":
    main()