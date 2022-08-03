/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2022 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <cassert>
#include <cstddef> // For offsetof()
#include <cstring> // For std::memset, std::memcmp
#include <iomanip>
#include <sstream>

#include "nnue/evaluate_nnue.h"

#include "bitboard.h"
#include "misc.h"
#include "movegen.h"
#include "position.h"
#include "thread.h"
#include "tt.h"
#include "uci.h"
#include "syzygy/tbprobe.h"

#include "tools/packed_sfen.h"
#include "tools/sfen_packer.h"

using std::string;

namespace Stockfish {

namespace Zobrist {

  Key psq[PIECE_NB][SQUARE_NB];
  Key side, noPawns;
  Key inHand[PIECE_NB][SQUARE_NB];
  Key checks[COLOR_NB][CHECKS_NB];
}


/// operator<<(Position) returns an ASCII representation of the position

std::ostream& operator<<(std::ostream& os, const Position& pos) {

  os << "\n ";
  for (File f = FILE_A; f <= pos.max_file(); ++f)
      os << "+---";
  os << "+\n";

  for (Rank r = pos.max_rank(); r >= RANK_1; --r)
  {
      for (File f = FILE_A; f <= pos.max_file(); ++f)
          if (pos.unpromoted_piece_on(make_square(f, r)))
              os << " |+" << pos.piece_to_char()[pos.unpromoted_piece_on(make_square(f, r))];
          else
              os << " | " << pos.piece_to_char()[pos.piece_on(make_square(f, r))];

      os << " |" << (1 + r);
      if (r == pos.max_rank() || r == RANK_1)
      {
          Color c = r == RANK_1 ? WHITE : BLACK;
          if (c == pos.side_to_move())
              os << " *";
          else
              os << "  ";
      }
      os << "\n ";
      for (File f = FILE_A; f <= pos.max_file(); ++f)
          os << "+---";
      os << "+\n";
  }

  for (File f = FILE_A; f <= pos.max_file(); ++f)
      os << "   " << char('a' + f);
  os << "\n";
  os << "\nFen: " << pos.fen() << "\nSfen: " << pos.fen(true) << "\nKey: " << std::hex << std::uppercase
     << std::setfill('0') << std::setw(16) << pos.key()
     << std::setfill(' ') << std::dec << "\nCheckers: ";

  for (Bitboard b = pos.checkers(); b; )
      os << UCI::square(pos, pop_lsb(b)) << " ";

  os << "\nChased: ";
  for (Bitboard b = pos.state()->chased; b; )
      os << UCI::square(pos, pop_lsb(b)) << " ";

  return os;
}


// Marcel van Kervinck's cuckoo algorithm for fast detection of "upcoming repetition"
// situations. Description of the algorithm in the following paper:
// https://marcelk.net/2013-04-06/paper/upcoming-rep-v2.pdf

// First and second hash functions for indexing the cuckoo tables
#ifdef LARGEBOARDS
inline int H1(Key h) { return h & 0x7fff; }
inline int H2(Key h) { return (h >> 16) & 0x7fff; }
#else
inline int H1(Key h) { return h & 0x1fff; }
inline int H2(Key h) { return (h >> 16) & 0x1fff; }
#endif

// Cuckoo tables with Zobrist hashes of valid reversible moves, and the moves themselves
#ifdef LARGEBOARDS
Key cuckoo[65536];
Move cuckooMove[65536];
#else
Key cuckoo[8192];
Move cuckooMove[8192];
#endif


/// Position::init() initializes at startup the various arrays used to compute hash keys

void Position::init() {

  PRNG rng(1070372);

  for (Color c : {WHITE, BLACK})
      for (PieceType pt = PAWN; pt <= KING; ++pt)
          for (Square s = SQ_A1; s <= SQ_MAX; ++s)
              Zobrist::psq[make_piece(c, pt)][s] = rng.rand<Key>();

  Zobrist::side = rng.rand<Key>();
  Zobrist::noPawns = rng.rand<Key>();

  for (Color c : {WHITE, BLACK})
      for (int n = 0; n < CHECKS_NB; ++n)
          Zobrist::checks[c][n] = rng.rand<Key>();

  for (Color c : {WHITE, BLACK})
      for (PieceType pt = PAWN; pt <= KING; ++pt)
          for (int n = 0; n < SQUARE_NB; ++n)
              Zobrist::inHand[make_piece(c, pt)][n] = rng.rand<Key>();

  // Prepare the cuckoo tables
  std::memset(cuckoo, 0, sizeof(cuckoo));
  std::memset(cuckooMove, 0, sizeof(cuckooMove));
  int count = 0;
  for (Color c : {WHITE, BLACK})
      for (PieceType pt = KNIGHT; pt <= QUEEN || pt == KING; pt != QUEEN ? ++pt : pt = KING)
      {
      Piece pc = make_piece(c, pt);
      for (Square s1 = SQ_A1; s1 <= SQ_MAX; ++s1)
          for (Square s2 = Square(s1 + 1); s2 <= SQ_MAX; ++s2)
              if ((type_of(pc) != PAWN) && (attacks_bb(c, type_of(pc), s1, 0) & s2))
              {
                  Move move = make_move(s1, s2);
                  Key key = Zobrist::psq[pc][s1] ^ Zobrist::psq[pc][s2] ^ Zobrist::side;
                  int i = H1(key);
                  while (true)
                  {
                      std::swap(cuckoo[i], key);
                      std::swap(cuckooMove[i], move);
                      if (move == MOVE_NONE) // Arrived at empty slot?
                          break;
                      i = (i == H1(key)) ? H2(key) : H1(key); // Push victim to alternative slot
                  }
                  count++;
             }
      }
#ifdef LARGEBOARDS
  assert(count == 9344);
#else
  assert(count == 3668);
#endif
}


/// Position::set() initializes the position object with the given FEN string.
/// This function is not very robust - make sure that input FENs are correct,
/// this is assumed to be the responsibility of the GUI.

Position& Position::set(const Variant* v, const string& fenStr, StateInfo* si, Thread* th, bool sfen) {
/*
   A FEN string defines a particular position using only the ASCII character set.

   A FEN string contains six fields separated by a space. The fields are:

   1) Piece placement (from white's perspective). Each rank is described, starting
      with rank 8 and ending with rank 1. Within each rank, the contents of each
      square are described from file A through file H. Following the Standard
      Algebraic Notation (SAN), each piece is identified by a single letter taken
      from the standard English names. White pieces are designated using upper-case
      letters ("PNBRQK") whilst Black uses lowercase ("pnbrqk"). Blank squares are
      noted using digits 1 through 8 (the number of blank squares), and "/"
      separates ranks.

   2) Active color. "w" means white moves next, "b" means black.

   3) Castling availability. If neither side can castle, this is "-". Otherwise,
      this has one or more letters: "K" (White can castle kingside), "Q" (White
      can castle queenside), "k" (Black can castle kingside), and/or "q" (Black
      can castle queenside).

   4) En passant target square (in algebraic notation). If there's no en passant
      target square, this is "-". If a pawn has just made a 2-square move, this
      is the position "behind" the pawn. Following X-FEN standard, this is recorded only
      if there is a pawn in position to make an en passant capture, and if there really
      is a pawn that might have advanced two squares.

   5) Halfmove clock. This is the number of halfmoves since the last pawn advance
      or capture. This is used to determine if a draw can be claimed under the
      fifty-move rule.

   6) Fullmove number. The number of the full move. It starts at 1, and is
      incremented after Black's move.
*/

  unsigned char col, row, token;
  size_t idx;
  std::istringstream ss(fenStr);

  std::memset(this, 0, sizeof(Position));
  std::memset(si, 0, sizeof(StateInfo));
  st = si;

  var = v;

  ss >> std::noskipws;

  Square sq = SQ_A1 + max_rank() * NORTH;

  // 1. Piece placement
  while ((ss >> token) && !isspace(token))
  {
      if (isdigit(token))
      {
#ifdef LARGEBOARDS
          if (isdigit(ss.peek()))
          {
              sq += 10 * (token - '0') * EAST;
              ss >> token;
          }
#endif
          sq += (token - '0') * EAST; // Advance the given number of files
      }

      else if (token == '/')
      {
          sq += 2 * SOUTH + (FILE_MAX - max_file()) * EAST;
          if (!is_ok(sq))
              break;
      }

      else if ((idx = piece_to_char().find(token)) != string::npos || (idx = piece_to_char_synonyms().find(token)) != string::npos)
      {
          if (ss.peek() == '~')
              ss >> token;
          put_piece(Piece(idx), sq, token == '~');
          ++sq;
      }

      // Stop before pieces in hand
      else if (token == '[')
          break;
  }
  // Pieces in hand
  if (!isspace(token))
      while ((ss >> token) && !isspace(token))
      {
          if (token == ']')
              continue;
          else if ((idx = piece_to_char().find(token)) != string::npos)
              add_to_hand(Piece(idx));
      }

  // 2. Active color
  ss >> token;
  sideToMove = (token != (sfen ? 'w' : 'b') ? WHITE : BLACK);  // Invert colors for SFEN
  ss >> token;

  // 3-4. Skip parsing castling and en passant flags if not present
  st->epSquare = SQ_NONE;
  st->castlingKingSquare[WHITE] = st->castlingKingSquare[BLACK] = SQ_NONE;
  if (!isdigit(ss.peek()) && !sfen)
  {
      // 3. Castling availability. Compatible with 3 standards: Normal FEN standard,
      // Shredder-FEN that uses the letters of the columns on which the rooks began
      // the game instead of KQkq and also X-FEN standard that, in case of Chess960,
      // if an inner rook is associated with the castling right, the castling tag is
      // replaced by the file letter of the involved rook, as for the Shredder-FEN.
      while ((ss >> token) && !isspace(token))
      {
          Square rsq;
          Color c = islower(token) ? BLACK : WHITE;
          Piece rook = make_piece(c, castling_rook_piece());

          token = char(toupper(token));

          if (token == 'K')
              for (rsq = make_square(FILE_MAX, castling_rank(c)); piece_on(rsq) != rook; --rsq) {}

          else if (token == 'Q')
              for (rsq = make_square(FILE_A, castling_rank(c)); piece_on(rsq) != rook; ++rsq) {}

          else if (token >= 'A' && token <= 'A' + max_file())
              rsq = make_square(File(token - 'A'), castling_rank(c));

          else
              continue;

          // Determine castling "king" position
          if (castling_enabled() && st->castlingKingSquare[c] == SQ_NONE)
          {
              Bitboard castlingKings = pieces(c, castling_king_piece()) & rank_bb(castling_rank(c));
              // Ambiguity resolution for 960 variants with more than one "king"
              // e.g., EAH means that an e-file king can castle with a- and h-file rooks
              st->castlingKingSquare[c] =  castlingKings && (!more_than_one(castlingKings)) ? lsb(castlingKings)
                                         : make_square(castling_king_file(), castling_rank(c));
          }

          if (castling_enabled() && piece_on(rsq) == rook)
              set_castling_right(c, rsq);
      }

      // 4. En passant square.
      // Ignore if square is invalid or not on side to move relative rank 6.
      if (   ((ss >> col) && (col >= 'a' && col <= 'a' + max_file()))
               && ((ss >> row) && (row >= '1' && row <= '1' + max_rank())))
      {
          st->epSquare = make_square(File(col - 'a'), Rank(row - '1'));

          // En passant square will be considered only if
          // a) side to move have a pawn threatening epSquare
          // b) there is an enemy pawn in front of epSquare
          // c) there is no piece on epSquare or behind epSquare
          bool enpassant;
          enpassant = pawn_attacks_bb(~sideToMove, st->epSquare) & pieces(sideToMove, PAWN)
                  && (pieces(~sideToMove, PAWN) & (st->epSquare + pawn_push(~sideToMove)))
                  && !(pieces() & (st->epSquare | (st->epSquare + pawn_push(sideToMove))));
          if (!enpassant)
              st->epSquare = SQ_NONE;
      }
  }

  // Check counter for nCheck
  ss >> std::skipws >> token >> std::noskipws;
  ss.putback(token);

  // 5-6. Halfmove clock and fullmove number
  if (sfen)
  {
      // Pieces in hand for SFEN
      int handCount = 1;
      while ((ss >> token) && !isspace(token))
      {
          if (token == '-')
              continue;
          else if (isdigit(token))
          {
              handCount = token - '0';
              while (isdigit(ss.peek()) && ss >> token)
                  handCount = 10 * handCount + (token - '0');
          }
          else if ((idx = piece_to_char().find(token)) != string::npos)
          {
              for (int i = 0; i < handCount; i++)
                  add_to_hand(Piece(idx));
              handCount = 1;
          }
      }
      // Move count is in ply for SFEN
      ss >> std::skipws >> gamePly;
      gamePly = std::max(gamePly - 1, 0);
  }
  else
  {
      ss >> std::skipws >> st->rule50 >> gamePly;

      // Convert from fullmove starting from 1 to gamePly starting from 0,
      // handle also common incorrect FEN with fullmove = 0.
      gamePly = std::max(2 * (gamePly - 1), 0) + (sideToMove == BLACK);
  }

  // counting rules
  if (st->countingLimit && st->rule50)
  {
      st->countingPly = st->rule50;
      st->rule50 = 0;
  }
  thisThread = th;
  set_state(st);

  assert(pos_is_ok());

  return *this;
}


/// Position::set_castling_right() is a helper function used to set castling
/// rights given the corresponding color and the rook starting square.

void Position::set_castling_right(Color c, Square rfrom) {

  assert(st->castlingKingSquare[c] != SQ_NONE);
  Square kfrom = st->castlingKingSquare[c];
  CastlingRights cr = c & (kfrom < rfrom ? KING_SIDE: QUEEN_SIDE);

  st->castlingRights |= cr;
  castlingRightsMask[kfrom] |= cr;
  castlingRightsMask[rfrom] |= cr;
  castlingRookSquare[cr] = rfrom;

  Square kto = make_square(cr & KING_SIDE ? castling_kingside_file() : castling_queenside_file(), castling_rank(c));
  Square rto = kto + (cr & KING_SIDE ? WEST : EAST);

  castlingPath[cr] =   (between_bb(rfrom, rto) | between_bb(kfrom, kto))
                    & ~(kfrom | rfrom);
}


/// Position::set_check_info() sets king attacks to detect if a move gives check

void Position::set_check_info(StateInfo* si) const {

  si->blockersForKing[WHITE] = slider_blockers(pieces(BLACK), count<KING>(WHITE) ? square<KING>(WHITE) : SQ_NONE, si->pinners[BLACK], BLACK);
  si->blockersForKing[BLACK] = slider_blockers(pieces(WHITE), count<KING>(BLACK) ? square<KING>(BLACK) : SQ_NONE, si->pinners[WHITE], WHITE);

  Square ksq = count<KING>(~sideToMove) ? square<KING>(~sideToMove) : SQ_NONE;

  // For unused piece types, the check squares are left uninitialized
  si->nonSlidingRiders = 0;
  for (PieceType pt : piece_types())
  {
      si->checkSquares[pt] = ksq != SQ_NONE ? attacks_bb(~sideToMove, pt, ksq, pieces()) : Bitboard(0);
      // Collect special piece types that require slower check and evasion detection
      if (AttackRiderTypes[pt] & NON_SLIDING_RIDERS)
          si->nonSlidingRiders |= pieces(pt);
  }
  si->shak = si->checkersBB & (byTypeBB[KNIGHT] | byTypeBB[ROOK] | byTypeBB[BERS]);
  si->bikjang = var->bikjangRule && ksq != SQ_NONE ? bool(attacks_bb(sideToMove, ROOK, ksq, pieces()) & pieces(sideToMove, KING)) : false;
  si->chased = var->chasingRule ? chased() : Bitboard(0);
  si->legalCapture = NO_VALUE;
  if (var->extinctionPseudoRoyal)
  {
      si->pseudoRoyals = 0;
      for (PieceType pt : extinction_piece_types())
      {
          if (count(sideToMove, pt) <= var->extinctionPieceCount + 1)
              si->pseudoRoyals |= pieces(sideToMove, pt);
          if (count(~sideToMove, pt) <= var->extinctionPieceCount + 1)
              si->pseudoRoyals |= pieces(~sideToMove, pt);
      }
  }
}


/// Position::set_state() computes the hash keys of the position, and other
/// data that once computed is updated incrementally as moves are made.
/// The function is only used when a new position is set up, and to verify
/// the correctness of the StateInfo data when running in debug mode.

void Position::set_state(StateInfo* si) const {

  si->key = si->materialKey = 0;
  si->pawnKey = Zobrist::noPawns;
  si->nonPawnMaterial[WHITE] = si->nonPawnMaterial[BLACK] = VALUE_ZERO;
  si->checkersBB = count<KING>(sideToMove) ? attackers_to(square<KING>(sideToMove), ~sideToMove) : Bitboard(0);
  si->move = MOVE_NONE;

  set_check_info(si);

  for (Bitboard b = pieces(); b; )
  {
      Square s = pop_lsb(b);
      Piece pc = piece_on(s);
      si->key ^= Zobrist::psq[pc][s];

      if (type_of(pc) == PAWN)
          si->pawnKey ^= Zobrist::psq[pc][s];

      else if (type_of(pc) != KING)
          si->nonPawnMaterial[color_of(pc)] += PieceValue[MG][pc];
  }

  if (sideToMove == BLACK)
      si->key ^= Zobrist::side;

  for (Color c : {WHITE, BLACK})
      for (PieceType pt = PAWN; pt <= KING; ++pt)
      {
          Piece pc = make_piece(c, pt);

          for (int cnt = 0; cnt < pieceCount[pc]; ++cnt)
              si->materialKey ^= Zobrist::psq[pc][cnt];
      }
}


/// Position::set() is an overload to initialize the position object with
/// the given endgame code string like "KBPKN". It is mainly a helper to
/// get the material key out of an endgame code.

Position& Position::set(const string& code, Color c, StateInfo* si) {

  assert(code[0] == 'K');

  string sides[] = { code.substr(code.find('K', 1)),      // Weak
                     code.substr(0, std::min(code.find('v'), code.find('K', 1))) }; // Strong

  assert(sides[0].length() > 0 && sides[0].length() < 8);
  assert(sides[1].length() > 0 && sides[1].length() < 8);

  std::transform(sides[c].begin(), sides[c].end(), sides[c].begin(), tolower);

  string n = std::to_string(FILE_NB);
  string fenStr =  n + "/" + sides[0] + char(FILE_NB - sides[0].length() + '0') + "/" + n + "/" + n + "/" + n + "/"
                 + n + "/" + sides[1] + char(FILE_NB - sides[1].length() + '0') + "/" + n + " w - - 0 10";

  return set(variants.find("fairy")->second, fenStr, si, nullptr);
}


/// Position::fen() returns a FEN representation of the position. In case of
/// Chess960 the Shredder-FEN notation is used. This is mainly a debugging function.

string Position::fen(bool sfen, bool showPromoted, int countStarted, std::string holdings) const {

  int emptyCnt;
  std::ostringstream ss;

  for (Rank r = max_rank(); r >= RANK_1; --r)
  {
      for (File f = FILE_A; f <= max_file(); ++f)
      {
          for (emptyCnt = 0; f <= max_file() && empty(make_square(f, r)); ++f)
              ++emptyCnt;

          if (emptyCnt)
              ss << emptyCnt;

          if (f <= max_file())
          {
              if (unpromoted_piece_on(make_square(f, r)))
                  // Promoted shogi pieces, e.g., +r for dragon
                  ss << "+" << piece_to_char()[unpromoted_piece_on(make_square(f, r))];
              else
              {
                  ss << piece_to_char()[piece_on(make_square(f, r))];

                  // Set promoted pieces
                  if (showPromoted && is_promoted(make_square(f, r)))
                      ss << "~";
              }
          }
      }

      if (r > RANK_1)
          ss << '/';
  }

  // SFEN
  if (sfen)
  {
      ss << (sideToMove == WHITE ? " b " : " w ");
      for (Color c : {WHITE, BLACK})
          for (PieceType pt = KING; pt >= PAWN; --pt)
              if (pieceCountInHand[c][pt] > 0)
              {
                  if (pieceCountInHand[c][pt] > 1)
                      ss << pieceCountInHand[c][pt];
                  ss << piece_to_char()[make_piece(c, pt)];
              }
      if (count_in_hand(ALL_PIECES) == 0)
          ss << '-';
      ss << " " << gamePly + 1;
      return ss.str();
  }

  ss << (sideToMove == WHITE ? " w " : " b ");
  if (!can_castle(ANY_CASTLING))
      ss << '-';

  // Counting limit or ep-square
  if (st->countingLimit)
      ss << " " << st->countingLimit << " ";
  else
      ss << (ep_square() == SQ_NONE ? " - " : " " + UCI::square(*this, ep_square()) + " ");

  ss << st->rule50;
  ss << " " << 1 + (gamePly - (sideToMove == BLACK)) / 2;

  return ss.str();
}


/// Position::slider_blockers() returns a bitboard of all the pieces (both colors)
/// that are blocking attacks on the square 's' from 'sliders'. A piece blocks a
/// slider if removing that piece from the board would result in a position where
/// square 's' is attacked. For example, a king-attack blocking piece can be either
/// a pinned or a discovered check piece, according if its color is the opposite
/// or the same of the color of the slider.

Bitboard Position::slider_blockers(Bitboard sliders, Square s, Bitboard& pinners, Color c) const {

  Bitboard blockers = 0;
  pinners = 0;

  if (s == SQ_NONE || !sliders)
      return blockers;

  // Snipers are sliders that attack 's' when a piece and other snipers are removed
  Bitboard snipers = 0;
  Bitboard slidingSnipers = 0;

  if (var->fastAttacks)
  {
      snipers = (  (attacks_bb<  ROOK>(s) & pieces(c, QUEEN, ROOK, CHANCELLOR))
                 | (attacks_bb<BISHOP>(s) & pieces(c, QUEEN, BISHOP, ARCHBISHOP))) & sliders;
      slidingSnipers = snipers;
  }
  else
  {
      for (PieceType pt : piece_types())
      {
          Bitboard b = sliders & (PseudoAttacks[~c][pt][s] ^ LeaperAttacks[~c][pt][s]) & pieces(c, pt);
          if (b)
          {
              // Consider asymmetrical moves (e.g., horse)
              if (AttackRiderTypes[pt] & ASYMMETRICAL_RIDERS)
              {
                  Bitboard asymmetricals = PseudoAttacks[~c][pt][s] & pieces(c, pt);
                  while (asymmetricals)
                  {
                      Square s2 = pop_lsb(asymmetricals);
                      if (!(attacks_from(c, pt, s2) & s))
                          snipers |= s2;
                  }
              }
              else
                  snipers |= b & ~attacks_bb(~c, pt, s, pieces());
              if (AttackRiderTypes[pt] & ~HOPPING_RIDERS)
                  slidingSnipers |= snipers & pieces(pt);
          }
      }
      // Diagonal rook pins in Janggi palace
      if (diagonal_lines() & s)
      {
          Bitboard diags = diagonal_lines() & PseudoAttacks[~c][BISHOP][s] & sliders & pieces(c, ROOK);
          while (diags)
          {
              Square s2 = pop_lsb(diags);
              if (!(attacks_from(c, ROOK, s2) & s))
              {
                  snipers |= s2;
                  slidingSnipers |= s2;
              }
          }
      }
  }
  Bitboard occupancy = pieces() ^ slidingSnipers;

  while (snipers)
  {
    Square sniperSq = pop_lsb(snipers);
    bool isHopper = AttackRiderTypes[type_of(piece_on(sniperSq))] & HOPPING_RIDERS;
    Bitboard b = between_bb(s, sniperSq, type_of(piece_on(sniperSq))) & (isHopper ? (pieces() ^ sniperSq) : occupancy);

    if (b && (!more_than_one(b) || (isHopper && popcount(b) == 2)))
    {
        // Janggi cannons block each other
        if ((pieces(JANGGI_CANNON) & sniperSq) && (pieces(JANGGI_CANNON) & b))
            b &= pieces(JANGGI_CANNON);
        blockers |= b;
        if (b & pieces(color_of(piece_on(s))))
            pinners |= sniperSq;
    }
  }
  return blockers;
}


/// Position::attackers_to() computes a bitboard of all pieces which attack a
/// given square. Slider attacks use the occupied bitboard to indicate occupancy.

Bitboard Position::attackers_to(Square s, Bitboard occupied, Color c, Bitboard janggiCannons) const {

  // Use a faster version for variants with moderate rule variations
  if (var->fastAttacks)
  {
      return  (pawn_attacks_bb(~c, s)          & pieces(c, PAWN))
            | (attacks_bb<KNIGHT>(s)           & pieces(c, KNIGHT, ARCHBISHOP, CHANCELLOR))
            | (attacks_bb<  ROOK>(s, occupied) & pieces(c, ROOK, QUEEN, CHANCELLOR))
            | (attacks_bb<BISHOP>(s, occupied) & pieces(c, BISHOP, QUEEN, ARCHBISHOP))
            | (attacks_bb<KING>(s)             & pieces(c, KING, COMMONER));
  }

  // Use a faster version for selected fairy pieces
  if (var->fastAttacks2)
  {
      return  (pawn_attacks_bb(~c, s)             & pieces(c, PAWN, BREAKTHROUGH_PIECE, GOLD))
            | (attacks_bb<KNIGHT>(s)              & pieces(c, KNIGHT))
            | (attacks_bb<  ROOK>(s, occupied)    & (  pieces(c, ROOK, QUEEN, DRAGON)
                                                     | (pieces(c, LANCE) & PseudoAttacks[~c][LANCE][s])))
            | (attacks_bb<BISHOP>(s, occupied)    & pieces(c, BISHOP, QUEEN, DRAGON_HORSE))
            | (attacks_bb<KING>(s)                & pieces(c, KING, COMMONER))
            | (attacks_bb<FERS>(s)                & pieces(c, FERS, DRAGON, SILVER))
            | (attacks_bb<WAZIR>(s)               & pieces(c, WAZIR, DRAGON_HORSE, GOLD))
            | (LeaperAttacks[~c][SHOGI_KNIGHT][s] & pieces(c, SHOGI_KNIGHT))
            | (LeaperAttacks[~c][SHOGI_PAWN][s]   & pieces(c, SHOGI_PAWN, SILVER));
  }

  Bitboard b = 0;
  for (PieceType pt : piece_types())
      if (board_bb(c, pt) & s)
      {
          PieceType move_pt = pt == KING ? king_type() : pt;
          // Consider asymmetrical moves (e.g., horse)
          if (AttackRiderTypes[move_pt] & ASYMMETRICAL_RIDERS)
          {
              Bitboard asymmetricals = PseudoAttacks[~c][move_pt][s] & pieces(c, pt);
              while (asymmetricals)
              {
                  Square s2 = pop_lsb(asymmetricals);
                  if (attacks_bb(c, move_pt, s2, occupied) & s)
                      b |= s2;
              }
          }
          else
              b |= attacks_bb(~c, move_pt, s, occupied) & pieces(c, pt);
      }

  // Consider special move of neang in cambodian chess
  if (cambodian_moves())
  {
      Square fers_sq = s + 2 * (c == WHITE ? SOUTH : NORTH);
      if (is_ok(fers_sq))
          b |= pieces(c, FERS) & gates(c) & fers_sq;
  }

  // Janggi palace moves
  if (diagonal_lines() & s)
  {
      Bitboard diags = 0;
      if (king_type() == WAZIR)
          diags |= attacks_bb(~c, FERS, s, occupied) & pieces(c, KING);
      diags |= attacks_bb(~c, FERS, s, occupied) & pieces(c, WAZIR);
      diags |= attacks_bb(~c, PAWN, s, occupied) & pieces(c, SOLDIER);
      diags |= rider_attacks_bb<RIDER_BISHOP>(s, occupied) & pieces(c, ROOK);
      diags |=  rider_attacks_bb<RIDER_CANNON_DIAG>(s, occupied)
              & rider_attacks_bb<RIDER_CANNON_DIAG>(s, occupied & ~janggiCannons)
              & pieces(c, JANGGI_CANNON);
      b |= diags & diagonal_lines();
  }

  // Unpromoted soldiers
  if (b & pieces(SOLDIER) && relative_rank(c, s, max_rank()) < var->soldierPromotionRank)
      b ^= b & pieces(SOLDIER) & ~PseudoAttacks[~c][SHOGI_PAWN][s];

  return b;
}


Bitboard Position::attackers_to(Square s, Bitboard occupied) const {
  return attackers_to(s, occupied, WHITE) | attackers_to(s, occupied, BLACK);
}

/// Position::attackers_to_pseudo_royals computes a bitboard of all pieces
/// of a particular color attacking at least one opposing pseudo-royal piece
Bitboard Position::attackers_to_pseudo_royals(Color c) const {
  Bitboard attackers = 0;
  Bitboard pseudoRoyals = st->pseudoRoyals & pieces(~c);
  Bitboard pseudoRoyalsTheirs = st->pseudoRoyals & pieces(c);
  while (pseudoRoyals) {
      Square sr = pop_lsb(pseudoRoyals);
      if (blast_on_capture()
          && pseudoRoyalsTheirs & attacks_bb<KING>(sr))
          // skip if capturing this piece would blast all of the attacker's pseudo-royal pieces
          continue;
      attackers |= attackers_to(sr, c);
  }
  return attackers;
}


/// Position::legal() tests whether a pseudo-legal move is legal

bool Position::legal(Move m) const {

  assert(is_ok(m));
  assert(piece_drops());

  Color us = sideToMove;
  Square from = from_sq(m);
  Square to = to_sq(m);

  assert(color_of(moved_piece(m)) == us);
  assert(!count<KING>(us) || piece_on(square<KING>(us)) == make_piece(us, KING));
  assert(board_bb() & to);

  // Illegal checks
  if (!checking_permitted() && gives_check(m))
      return false;

  // Illegal quiet moves
  if (must_capture() && !capture(m) && has_capture())
      return false;

  // No legal moves from target square
  if (immobility_illegal() && !(moves_bb(us, type_of(moved_piece(m)), to, 0) & board_bb()))
      return false;

  // Check for attacks to pseudo-royal pieces
  if (var->extinctionPseudoRoyal)
  {
      Square kto = to;
      Bitboard occupied = (pieces() ^ from) | kto;
      if (capture(m) && blast_on_capture())
          occupied &= ~((attacks_bb<KING>(kto) & (pieces() ^ pieces(PAWN))) | kto);
      Bitboard pseudoRoyals = st->pseudoRoyals & pieces(sideToMove);
      Bitboard pseudoRoyalsTheirs = st->pseudoRoyals & pieces(~sideToMove);
      if (is_ok(from) && (pseudoRoyals & from))
          pseudoRoyals ^= square_bb(from) ^ kto;
      // Self-explosions are illegal
      if (pseudoRoyals & ~occupied)
          return false;
      // Check for legality unless we capture a pseudo-royal piece
      if (!(pseudoRoyalsTheirs & ~occupied))
          while (pseudoRoyals)
          {
              Square sr = pop_lsb(pseudoRoyals);
              // Touching pseudo-royal pieces are immune
              if (  !(blast_on_capture() && (pseudoRoyalsTheirs & attacks_bb<KING>(sr)))
                  && (attackers_to(sr, occupied, ~us) & (occupied & ~square_bb(kto))))
                  return false;
          }
  }

  Bitboard occupied = (pieces() ^ from) | to;

  // Flying general rule
  // In case of bikjang passing is always allowed, even when in check
  if (count<KING>(us))
  {
      Square s = type_of(moved_piece(m)) == KING ? to : square<KING>(us);
      if (attacks_bb(~us, ROOK, s, occupied) & pieces(~us, KING) & ~square_bb(to))
          return false;
  }

  // If the moving piece is a king, check whether the destination square is
  // attacked by the opponent.
  if (type_of(moved_piece(m)) == KING)
      return !attackers_to(to, occupied, ~us);

  // Return early when without king
  if (!count<KING>(us))
      return true;

  Bitboard janggiCannons = pieces(JANGGI_CANNON);
  if (type_of(moved_piece(m)) == JANGGI_CANNON)
      janggiCannons = janggiCannons | to;
  else if (janggiCannons & to)
      janggiCannons ^= to;

  // A non-king move is legal if the king is not under attack after the move.
  return !(attackers_to(square<KING>(us), occupied, ~us, janggiCannons) & ~SquareBB[to]);
}


/// Position::pseudo_legal() takes a random move and tests whether the move is
/// pseudo legal. It is used to validate moves from TT that can be corrupted
/// due to SMP concurrent access or hash position key aliasing.

bool Position::pseudo_legal(const Move m) const {

  Color us = sideToMove;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = moved_piece(m);

  // Illegal moves to squares outside of board
  if (!(board_bb() & to))
      return false;

  // Use a slower but simpler function for uncommon cases
  // yet we skip the legality check of MoveList<LEGAL>().
  if (type_of(m) != NORMAL)
      return checkers() ? MoveList<    EVASIONS>(*this).contains(m)
                        : MoveList<NON_EVASIONS>(*this).contains(m);

  // Handle the case where a mandatory piece promotion/demotion is not taken
  if (    mandatory_piece_promotion()
      && (is_promoted(from) ? piece_demotion() : promoted_piece_type(type_of(pc)) != NO_PIECE_TYPE)
      && (zone_bb(us, promotion_rank(), max_rank()) & (SquareBB[from] | to))
      && (!piece_promotion_on_capture() || capture(m)))
      return false;

  // If the 'from' square is not occupied by a piece belonging to the side to
  // move, the move is obviously not legal.
  if (pc == NO_PIECE || color_of(pc) != us)
      return false;

  // The destination square cannot be occupied by a friendly piece
  if (pieces(us) & to)
      return false;

  // Handle the special case of a pawn move
  if (type_of(pc) == PAWN)
  {
      // We have already handled promotion moves, so destination
      // cannot be on the 8th/1st rank.
      if (mandatory_pawn_promotion() && rank_of(to) == relative_rank(us, promotion_rank(), max_rank()) && !sittuyin_promotion())
          return false;

      if (   !(pawn_attacks_bb(us, from) & pieces(~us) & to) // Not a capture
          && !((from + pawn_push(us) == to) && empty(to))       // Not a single push
          && !(   (from + 2 * pawn_push(us) == to)              // Not a double push
               && (   relative_rank(us, from, max_rank()) <= double_step_rank_max()
                   && relative_rank(us, from, max_rank()) >= double_step_rank_min())
               && empty(to)
               && empty(to - pawn_push(us))
               && double_step_enabled()))
          return false;
  }
  else if (!((capture(m) ? attacks_from(us, type_of(pc), from) : moves_from(us, type_of(pc), from)) & to))
      return false;

  // Evasions generator already takes care to avoid some kind of illegal moves
  // and legal() relies on this. We therefore have to take care that the same
  // kind of moves are filtered out here.
  if (checkers() && !(checkers() & non_sliding_riders()))
  {
      if (type_of(pc) != KING)
      {
          // Double check? In this case a king move is required
          if (more_than_one(checkers()))
              return false;

          // Our move must be a blocking evasion or a capture of the checking piece
          Square checksq = lsb(checkers());
          if (  !(between_bb(square<KING>(us), lsb(checkers())) & to)
              || ((LeaperAttacks[~us][type_of(piece_on(checksq))][checksq] & square<KING>(us)) && !(checkers() & to)))
              return false;
      }
      // In case of king moves under check we have to remove king so as to catch
      // invalid moves like b1a1 when opposite queen is on c1.
      else if (attackers_to(to, pieces() ^ from, ~us))
          return false;
  }

  return true;
}


/// Position::gives_check() tests whether a pseudo-legal move gives a check

bool Position::gives_check(Move m) const {

  assert(is_ok(m));
  assert(color_of(moved_piece(m)) == sideToMove);

  Square from = from_sq(m);
  Square to = to_sq(m);

  // No check possible without king
  if (!count<KING>(~sideToMove))
      return false;

  // Is there a direct check?
      PieceType pt = type_of(moved_piece(m));
      if (AttackRiderTypes[pt] & (HOPPING_RIDERS | ASYMMETRICAL_RIDERS))
      {
          Bitboard occupied = (pieces() ^ from) | to;
          if (attacks_bb(sideToMove, pt, to, occupied) & square<KING>(~sideToMove))
              return true;
      }
      else if (check_squares(pt) & to)
          return true;

  Bitboard janggiCannons = pieces(JANGGI_CANNON);
  if (type_of(moved_piece(m)) == JANGGI_CANNON)
      janggiCannons = (janggiCannons ^ from) | to;
  else if (janggiCannons & to)
      janggiCannons ^= to;

  // Is there a discovered check?
  if (  ((blockers_for_king(~sideToMove) & from)) || (non_sliding_riders() & pieces(sideToMove))
      && attackers_to(square<KING>(~sideToMove), (pieces() ^ from) | to, sideToMove, janggiCannons))
      return true;

  // Is there a check by special diagonal moves?
  if (more_than_one(diagonal_lines() & (to | square<KING>(~sideToMove))))
  {
      PieceType pt = type_of(moved_piece(m));
      PieceType diagType = pt == WAZIR ? FERS : pt == SOLDIER ? PAWN : pt == ROOK ? BISHOP : NO_PIECE_TYPE;
      Bitboard occupied = pieces() ^ from;
      if (diagType && (attacks_bb(sideToMove, diagType, to, occupied) & square<KING>(~sideToMove)))
          return true;
      else if (pt == JANGGI_CANNON && (  rider_attacks_bb<RIDER_CANNON_DIAG>(to, occupied)
                                       & rider_attacks_bb<RIDER_CANNON_DIAG>(to, occupied & ~janggiCannons)
                                       & square<KING>(~sideToMove)))
          return true;
  }

  return false;
}

/// Position::do_move() makes a move, and saves all information necessary
/// to a StateInfo object. The move is assumed to be legal. Pseudo-legal
/// moves should be filtered out before this function is called.

void Position::do_move(Move m, StateInfo& newSt, bool givesCheck) {

  assert(is_ok(m));
  assert(&newSt != st);

#ifndef NO_THREADS
  thisThread->nodes.fetch_add(1, std::memory_order_relaxed);
#endif
  Key k = st->key ^ Zobrist::side;

  // Copy some fields of the old state to our new StateInfo object except the
  // ones which are going to be recalculated from scratch anyway and then switch
  // our state pointer to point to the new (ready to be updated) state.
  std::memcpy(static_cast<void*>(&newSt), static_cast<void*>(st), offsetof(StateInfo, key));
  newSt.previous = st;
  st = &newSt;
  st->move = m;

  // Increment ply counters. In particular, rule50 will be reset to zero later on
  // in case of a capture or a pawn move.
  ++gamePly;
  ++st->rule50;
  ++st->pliesFromNull;
  if (st->countingLimit)
      ++st->countingPly;

  // Used by NNUE
  st->accumulator.computed[WHITE] = false;
  st->accumulator.computed[BLACK] = false;
  auto& dp = st->dirtyPiece;
  dp.dirty_num = 1;

  Color us = sideToMove;
  Color them = ~us;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = moved_piece(m);
  Piece captured = piece_on(to);
  st->capturedpromoted = is_promoted(to);
  st->unpromotedCapturedPiece = captured ? unpromoted_piece_on(to) : NO_PIECE;
  st->pass = false;

  assert(color_of(pc) == us);
  assert(captured == NO_PIECE || color_of(captured) == them);
  assert(type_of(captured) != KING);

  if (captured)
  {
      Square capsq = to;

      // If the captured piece is a pawn, update pawn hash key, otherwise
      // update non-pawn material.
      if (type_of(captured) == PAWN)
          st->pawnKey ^= Zobrist::psq[captured][capsq];
      else
          st->nonPawnMaterial[them] -= PieceValue[MG][captured];

      if (Eval::NNUE::useNNUE != Eval::NNUE::UseNNUEMode::False)
      {
          dp.dirty_num = 2;  // 1 piece moved, 1 piece captured
          dp.piece[1] = captured;
          dp.from[1] = capsq;
          dp.to[1] = SQ_NONE;
      }

      // Update board and piece lists
      bool capturedPromoted = is_promoted(capsq);
      Piece unpromotedCaptured = unpromoted_piece_on(capsq);
      remove_piece(capsq);

      if (Eval::NNUE::useNNUE != Eval::NNUE::UseNNUEMode::False)
          dp.handPiece[1] = NO_PIECE;

      // Update material hash key and prefetch access to materialTable
      k ^= Zobrist::psq[captured][capsq];
      st->materialKey ^= Zobrist::psq[captured][pieceCount[captured]];
#ifndef NO_THREADS
      prefetch(thisThread->materialTable[st->materialKey]);
#endif
      // Reset rule 50 counter
      st->rule50 = 0;
  }
  k ^= Zobrist::psq[pc][from] ^ Zobrist::psq[pc][to];

  // Flip enclosed pieces
  st->flippedPieces = 0;
  if (flip_enclosed_pieces())
  {
      // Find end of rows to be flipped
      if (flip_enclosed_pieces() == REVERSI)
      {
          Bitboard b = attacks_bb(us, QUEEN, to, board_bb() & ~pieces(~us)) & ~PseudoAttacks[us][KING][to] & pieces(us);
          while(b)
              st->flippedPieces |= between_bb(pop_lsb(b), to) ^ to;
      }
      else
      {
          assert(flip_enclosed_pieces() == ATAXX);
          st->flippedPieces = PseudoAttacks[us][KING][to] & pieces(~us);
      }

      // Flip pieces
      Bitboard to_flip = st->flippedPieces;
      while(to_flip)
      {
          Square s = pop_lsb(to_flip);
          Piece flipped = piece_on(s);
          Piece resulting = ~flipped;

          // remove opponent's piece
          remove_piece(s);
          k ^= Zobrist::psq[flipped][s];
          st->materialKey ^= Zobrist::psq[flipped][pieceCount[flipped]];
          st->nonPawnMaterial[them] -= PieceValue[MG][flipped];

          // add our piece
          put_piece(resulting, s);
          k ^= Zobrist::psq[resulting][s];
          st->materialKey ^= Zobrist::psq[resulting][pieceCount[resulting]-1];
          st->nonPawnMaterial[us] += PieceValue[MG][resulting];
      }
  }

  // Move the piece.
      if (Eval::NNUE::useNNUE != Eval::NNUE::UseNNUEMode::False)
      {
          dp.piece[0] = pc;
          dp.from[0] = from;
          dp.to[0] = to;
      }

      move_piece(from, to);
  // If the moving piece is a pawn do some special extra work
  if (type_of(pc) == PAWN)
  {
      // Update pawn hash key
      st->pawnKey ^= Zobrist::psq[pc][from] ^ Zobrist::psq[pc][to];

      // Reset rule 50 draw counter
      st->rule50 = 0;
  }

  // Set capture piece
  st->capturedPiece = captured;

  // Remove the blast pieces
  if (captured && blast_on_capture())
  {
      std::memset(st->unpromotedBycatch, 0, sizeof(st->unpromotedBycatch));
      st->demotedBycatch = st->promotedBycatch = 0;
      Bitboard blast = (attacks_bb<KING>(to) & (pieces() ^ pieces(PAWN))) | to;
      while (blast)
      {
          Square bsq = pop_lsb(blast);
          Piece bpc = piece_on(bsq);
          Color bc = color_of(bpc);
          if (type_of(bpc) != PAWN)
              st->nonPawnMaterial[bc] -= PieceValue[MG][bpc];

          if (Eval::NNUE::useNNUE != Eval::NNUE::UseNNUEMode::False)
          {
              dp.piece[dp.dirty_num] = bpc;
              dp.handPiece[dp.dirty_num] = NO_PIECE;
              dp.from[dp.dirty_num] = bsq;
              dp.to[dp.dirty_num] = SQ_NONE;
              dp.dirty_num++;
          }

          // Update board and piece lists
          // In order to not have to store the values of both board and unpromotedBoard,
          // demote promoted pieces, but keep promoted pawns as promoted,
          // and store demotion/promotion bitboards to disambiguate the piece state
          bool capturedPromoted = is_promoted(bsq);
          Piece unpromotedCaptured = unpromoted_piece_on(bsq);
          st->unpromotedBycatch[bsq] = unpromotedCaptured ? unpromotedCaptured : bpc;
          if (unpromotedCaptured)
              st->demotedBycatch |= bsq;
          else if (capturedPromoted)
              st->promotedBycatch |= bsq;
          remove_piece(bsq);
          board[bsq] = NO_PIECE;

          // Update material hash key
          k ^= Zobrist::psq[bpc][bsq];
          st->materialKey ^= Zobrist::psq[bpc][pieceCount[bpc]];
          if (type_of(bpc) == PAWN)
              st->pawnKey ^= Zobrist::psq[bpc][bsq];
      }
  }

  // Update the key with the final value
  st->key = k;
  // Calculate checkers bitboard (if move gives check)
  st->checkersBB = givesCheck ? attackers_to(square<KING>(them), us) & pieces(us) : Bitboard(0);

  sideToMove = ~sideToMove;

  // Update king attacks used for fast check detection
  set_check_info(st);

  // Calculate the repetition info. It is the ply distance from the previous
  // occurrence of the same position, negative in the 3-fold case, or zero
  // if the position was not repeated.
  st->repetition = 0;
  int end = std::min(st->rule50, st->pliesFromNull);
  if (end >= 4)
  {
      StateInfo* stp = st->previous->previous;
      for (int i = 4; i <= end; i += 2)
      {
          stp = stp->previous->previous;
          if (stp->key == st->key)
          {
              st->repetition = stp->repetition ? -i : i;
              break;
          }
      }
  }

  assert(pos_is_ok());
}


/// Position::undo_move() unmakes a move. When it returns, the position should
/// be restored to exactly the same state as before the move was made.

void Position::undo_move(Move m) {

  assert(is_ok(m));

  sideToMove = ~sideToMove;

  Color us = sideToMove;
  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = piece_on(to);

  assert(empty(from));
  assert(type_of(st->capturedPiece) != KING);

  // Add the blast pieces
  if (st->capturedPiece && blast_on_capture())
  {
      Bitboard blast = attacks_bb<KING>(to) | to;
      while (blast)
      {
          Square bsq = pop_lsb(blast);
          Piece unpromotedBpc = st->unpromotedBycatch[bsq];
          Piece bpc = st->demotedBycatch & bsq ? make_piece(color_of(unpromotedBpc), promoted_piece_type(type_of(unpromotedBpc)))
                                               : unpromotedBpc;
          bool isPromoted = (st->promotedBycatch | st->demotedBycatch) & bsq;

          // Update board and piece lists
          if (bpc)
          {
              put_piece(bpc, bsq, isPromoted, st->demotedBycatch & bsq ? unpromotedBpc : NO_PIECE);
          }
      }
      // Reset piece since it exploded itself
      pc = piece_on(to);
  }

  move_piece(to, from); // Put the piece back at the source square

  if (st->capturedPiece)
  {
      Square capsq = to;

      put_piece(st->capturedPiece, capsq, st->capturedpromoted, st->unpromotedCapturedPiece); // Restore the captured piece
  }

  if (flip_enclosed_pieces())
  {
      // Flip pieces
      Bitboard to_flip = st->flippedPieces;
      while(to_flip)
      {
          Square s = pop_lsb(to_flip);
          Piece resulting = ~piece_on(s);
          remove_piece(s);
          put_piece(resulting, s);
      }
  }

  // Finally point our state pointer back to the previous state
  st = st->previous;
  --gamePly;

  assert(pos_is_ok());
}


/// Position::do_castling() is a helper used to do/undo a castling move. This
/// is a bit tricky in Chess960 where from/to squares can overlap.
template<bool Do>
void Position::do_castling(Color us, Square from, Square& to, Square& rfrom, Square& rto) {

  bool kingSide = to > from;
  rfrom = to; // Castling is encoded as "king captures friendly rook"
  to = make_square(kingSide ? castling_kingside_file() : castling_queenside_file(), castling_rank(us));
  rto = to + (kingSide ? WEST : EAST);

  Piece castlingKingPiece = piece_on(Do ? from : to);
  Piece castlingRookPiece = piece_on(Do ? rfrom : rto);

  if (Do && Eval::NNUE::useNNUE != Eval::NNUE::UseNNUEMode::False)
  {
      auto& dp = st->dirtyPiece;
      dp.piece[0] = castlingKingPiece;
      dp.from[0] = from;
      dp.to[0] = to;
      dp.piece[1] = castlingRookPiece;
      dp.from[1] = rfrom;
      dp.to[1] = rto;
      dp.dirty_num = 2;
  }

  // Remove both pieces first since squares could overlap in Chess960
  remove_piece(Do ? from : to);
  remove_piece(Do ? rfrom : rto);
  board[Do ? from : to] = board[Do ? rfrom : rto] = NO_PIECE; // Since remove_piece doesn't do it for us
  put_piece(castlingKingPiece, Do ? to : from);
  put_piece(castlingRookPiece, Do ? rto : rfrom);
}


/// Position::do_null_move() is used to do a "null move": it flips
/// the side to move without executing any move on the board.

void Position::do_null_move(StateInfo& newSt) {

  assert(!checkers());
  assert(&newSt != st);

  std::memcpy(&newSt, st, offsetof(StateInfo, accumulator));

  newSt.previous = st;
  st = &newSt;

  // Used by NNUE
  st->dirtyPiece.dirty_num = 0;
  st->dirtyPiece.piece[0] = NO_PIECE; // Avoid checks in UpdateAccumulator()
  st->accumulator.computed[WHITE] = false;
  st->accumulator.computed[BLACK] = false;

  st->key ^= Zobrist::side;
  prefetch(TT.first_entry(key()));

  ++st->rule50;
  st->pliesFromNull = 0;

  sideToMove = ~sideToMove;

  set_check_info(st);

  st->repetition = 0;

  assert(pos_is_ok());
}


/// Position::undo_null_move() must be used to undo a "null move"

void Position::undo_null_move() {

  assert(!checkers());

  st = st->previous;
  sideToMove = ~sideToMove;
}


/// Position::key_after() computes the new hash key after the given move. Needed
/// for speculative prefetch. It doesn't recognize special moves like castling,
/// en passant and promotions.

Key Position::key_after(Move m) const {

  Square from = from_sq(m);
  Square to = to_sq(m);
  Piece pc = moved_piece(m);
  Piece captured = piece_on(to);
  Key k = st->key ^ Zobrist::side;

  if (captured)
  {
      k ^= Zobrist::psq[captured][to];
  }

  return k ^ Zobrist::psq[pc][to] ^ Zobrist::psq[pc][from];
}


Value Position::blast_see(Move m) const {
  assert(is_ok(m));

  Square from = from_sq(m);
  Square to = to_sq(m);
  Color us = color_of(moved_piece(m));
  Bitboard fromto = from | to;
  Bitboard blast = ((attacks_bb<KING>(to) & ~pieces(PAWN)) | fromto) & pieces();

  Value result = VALUE_ZERO;

  // Add the least valuable attacker for quiet moves
  if (!capture(m))
  {
      Bitboard attackers = attackers_to(to, pieces() ^ fromto, ~us);
      Value minAttacker = VALUE_INFINITE;

      while (attackers)
      {
          Square s = pop_lsb(attackers);
          if (extinction_piece_types().find(type_of(piece_on(s))) == extinction_piece_types().end())
              minAttacker = std::min(minAttacker, blast & s ? VALUE_ZERO : CapturePieceValue[MG][piece_on(s)]);
      }

      if (minAttacker == VALUE_INFINITE)
          return VALUE_ZERO;

      result += minAttacker;
  }

  // Sum up blast piece values
  while (blast)
  {
      Piece bpc = piece_on(pop_lsb(blast));
      if (extinction_piece_types().find(type_of(bpc)) != extinction_piece_types().end())
          return color_of(bpc) == us ?  extinction_value()
                        : capture(m) ? -extinction_value()
                                     : VALUE_ZERO;
      result += color_of(bpc) == us ? -CapturePieceValue[MG][bpc] : CapturePieceValue[MG][bpc];
  }

  return capture(m) || must_capture() ? result - 1 : std::min(result, VALUE_ZERO);
}


/// Position::see_ge (Static Exchange Evaluation Greater or Equal) tests if the
/// SEE value of move is greater or equal to the given threshold. We'll use an
/// algorithm similar to alpha-beta pruning with a null window.

bool Position::see_ge(Move m, Value threshold) const {

  assert(is_ok(m));

  Square from = from_sq(m), to = to_sq(m);

  // Atomic explosion SEE
  if (blast_on_capture())
      return blast_see(m) >= threshold;

  // Extinction
  if (   extinction_value() != VALUE_NONE
      && piece_on(to)
      && (   (   extinction_piece_types().find(type_of(piece_on(to))) != extinction_piece_types().end()
              && pieceCount[piece_on(to)] == extinction_piece_count() + 1)
          || (   extinction_piece_types().find(ALL_PIECES) != extinction_piece_types().end()
              && count<ALL_PIECES>(~sideToMove) == extinction_piece_count() + 1)))
      return extinction_value() < VALUE_ZERO;

  // Do not evaluate SEE if value would be unreliable
  if (must_capture() || !checking_permitted() || count<CLOBBER_PIECE>() == count<ALL_PIECES>())
      return VALUE_ZERO >= threshold;

  int swap = PieceValue[MG][piece_on(to)] - threshold;
  if (swap < 0)
      return false;

  swap = PieceValue[MG][moved_piece(m)] - swap;
  if (swap <= 0)
      return true;

  Bitboard occupied = (pieces() ^ from) ^ to;
  Color stm = color_of(moved_piece(m));
  Bitboard attackers = attackers_to(to, occupied);
  Bitboard stmAttackers, bb;
  int res = 1;
  if (attackers & pieces(stm, KING))
          attackers |= attacks_bb(stm, ROOK, to, occupied & ~pieces(ROOK)) & pieces(~stm, KING);
  if (attackers & pieces(~stm, KING))
          attackers |= attacks_bb(~stm, ROOK, to, occupied & ~pieces(ROOK)) & pieces(stm, KING);


  while (true)
  {
      stm = ~stm;
      attackers &= occupied;

      // If stm has no more attackers then give up: stm loses
      if (!(stmAttackers = attackers & pieces(stm)))
          break;

      // Don't allow pinned pieces to attack as long as there are
      // pinners on their original square.
      if (pinners(~stm) & occupied)
          stmAttackers &= ~blockers_for_king(stm);

      if (!stmAttackers)
          break;

      res ^= 1;

      // Locate and remove the next least valuable attacker, and add to
      // the bitboard 'attackers' any X-ray attackers behind it.
      if ((bb = stmAttackers & pieces(PAWN)))
      {
          if ((swap = PawnValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          attackers |= attacks_bb<BISHOP>(to, occupied) & pieces(BISHOP, QUEEN);
      }

      else if ((bb = stmAttackers & pieces(KNIGHT)))
      {
          if ((swap = KnightValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
      }

      else if ((bb = stmAttackers & pieces(BISHOP)))
      {
          if ((swap = BishopValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          attackers |= attacks_bb<BISHOP>(to, occupied) & pieces(BISHOP, QUEEN);
      }

      else if ((bb = stmAttackers & pieces(ROOK)))
      {
          if ((swap = RookValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          attackers |= attacks_bb<ROOK>(to, occupied) & pieces(ROOK, QUEEN);
      }

      else if ((bb = stmAttackers & pieces(QUEEN)))
      {
          if ((swap = QueenValueMg - swap) < res)
              break;

          occupied ^= least_significant_square_bb(bb);
          attackers |=  (attacks_bb<BISHOP>(to, occupied) & pieces(BISHOP, QUEEN))
                      | (attacks_bb<ROOK  >(to, occupied) & pieces(ROOK  , QUEEN));
      }

      // fairy pieces
      // pick next piece without considering value
      else if ((bb = stmAttackers & ~pieces(KING)))
      {
          if ((swap = PieceValue[MG][piece_on(lsb(bb))] - swap) < res)
              break;

          occupied ^= lsb(bb);
      }

      else // KING
           // If we "capture" with the king but opponent still has attackers,
           // reverse the result.
          return (attackers & ~pieces(stm)) ? res ^ 1 : res;
  }

  return bool(res);
}

/// Position::is_optinal_game_end() tests whether the position may end the game by
/// 50-move rule, by repetition, or a variant rule that allows a player to claim a game result.

bool Position::is_optional_game_end(Value& result, int ply, int countStarted) const {

  // n-fold repetition
  if (n_fold_rule())
  {
      int end = std::min(st->rule50, st->pliesFromNull);

      if (end >= 4)
      {
          StateInfo* stp = st->previous->previous;
          int cnt = 0;
          bool perpetualThem = st->checkersBB && stp->checkersBB;
          bool perpetualUs = st->previous->checkersBB && stp->previous->checkersBB;
          Bitboard chaseThem = undo_move_board(st->chased, st->previous->move) & stp->chased;
          Bitboard chaseUs = undo_move_board(st->previous->chased, stp->move) & stp->previous->chased;
          int moveRepetition = var->moveRepetitionIllegal
                               && type_of(st->move) == NORMAL
                               && !st->previous->checkersBB && !stp->previous->checkersBB
                               && (board_bb(~side_to_move(), type_of(piece_on(to_sq(st->move)))) & board_bb(side_to_move(), KING))
                               ? (stp->move == reverse_move(st->move) ? 2 : 0) : 0;

          for (int i = 4; i <= end; i += 2)
          {
              // Janggi repetition rule
              if (moveRepetition > 0)
              {
                  if (i + 1 <= end && stp->previous->previous->previous->checkersBB)
                      moveRepetition = 0;
                  else if (moveRepetition < 4)
                  {
                      if (stp->previous->previous->move == reverse_move((moveRepetition == 1 ? st : stp)->move))
                          moveRepetition++;
                      else
                          moveRepetition = 0;
                  }
                  else
                  {
                      assert(moveRepetition == 4);
                      if (!stp->previous->previous->capturedPiece && from_sq(stp->move) == to_sq(stp->previous->previous->move))
                      {
                          result = VALUE_MATE;
                          return true;
                      }
                      else
                          moveRepetition = 0;
                  }
              }
              // Chased pieces are empty when there is no previous move
              if (i != st->pliesFromNull)
                  chaseThem = undo_move_board(chaseThem, stp->previous->move) & stp->previous->previous->chased;
              stp = stp->previous->previous;
              perpetualThem &= bool(stp->checkersBB);

              // Return a draw score if a position repeats once earlier but strictly
              // after the root, or repeats twice before or at the root.
              if (   stp->key == st->key
                  && ++cnt + 1 == (ply > i && !var->moveRepetitionIllegal ? 2 : n_fold_rule()))
              {
                  result = convert_mate_value(  var->perpetualCheckIllegal && (perpetualThem || perpetualUs) ? (!perpetualUs ? VALUE_MATE : !perpetualThem ? -VALUE_MATE : VALUE_DRAW)
                                              : var->chasingRule && (chaseThem || chaseUs) ? (!chaseUs ? VALUE_MATE : !chaseThem ? -VALUE_MATE : VALUE_DRAW)
                                              : var->nFoldValueAbsolute && sideToMove == BLACK ? -var->nFoldValue
                                              : var->nFoldValue, ply);
                  if (result == VALUE_DRAW && var->materialCounting)
                      result = convert_mate_value(material_counting_result(), ply);
                  return true;
              }

              if (i + 1 <= end)
              {
                  perpetualUs &= bool(stp->previous->checkersBB);
                  chaseUs = undo_move_board(chaseUs, stp->move) & stp->previous->chased;
              }
          }
      }
  }

  return false;
}

/// Position::is_immediate_game_end() tests whether the position ends the game
/// immediately by a variant rule, i.e., there are no more legal moves.
/// It does not not detect stalemates.

bool Position::is_immediate_game_end(Value& result, int ply) const {

  // Extinction
  // Extinction does not apply for pseudo-royal pieces, because they can not be captured
  if (extinction_value() != VALUE_NONE && (!var->extinctionPseudoRoyal || blast_on_capture()))
  {
      for (Color c : { ~sideToMove, sideToMove })
          for (PieceType pt : extinction_piece_types())
              if (   count_with_hand( c, pt) <= var->extinctionPieceCount
                  && count_with_hand(~c, pt) >= var->extinctionOpponentPieceCount + (extinction_claim() && c == sideToMove))
              {
                  result = c == sideToMove ? extinction_value(ply) : -extinction_value(ply);
                  return true;
              }
  }
  // capture the flag
  if (   capture_the_flag_piece()
      && flag_move()
      && (capture_the_flag(sideToMove) & pieces(sideToMove, capture_the_flag_piece())))
  {
      result =  (capture_the_flag(~sideToMove) & pieces(~sideToMove, capture_the_flag_piece()))
              && sideToMove == WHITE ? VALUE_DRAW : mate_in(ply);
      return true;
  }
  if (   capture_the_flag_piece()
      && (!flag_move() || capture_the_flag_piece() == KING)
      && (capture_the_flag(~sideToMove) & pieces(~sideToMove, capture_the_flag_piece())))
  {
      bool gameEnd = true;
      // Check whether king can move to CTF zone
      if (   flag_move() && sideToMove == BLACK && !checkers() && count<KING>(sideToMove)
          && (capture_the_flag(sideToMove) & attacks_from(sideToMove, KING, square<KING>(sideToMove))))
      {
          assert(capture_the_flag_piece() == KING);
          gameEnd = true;
          for (const auto& m : MoveList<NON_EVASIONS>(*this))
              if (type_of(moved_piece(m)) == KING && (capture_the_flag(sideToMove) & to_sq(m)) && legal(m))
              {
                  gameEnd = false;
                  break;
              }
      }
      if (gameEnd)
      {
          result = mated_in(ply);
          return true;
      }
  }
  // Connect-n
  if (connect_n() > 0)
  {
      Bitboard b;
      for (Direction d : {NORTH, NORTH_EAST, EAST, SOUTH_EAST})
      {
          b = pieces(~sideToMove);
          for (int i = 1; i < connect_n() && b; i++)
              b &= shift(d, b);
          if (b)
          {
              result = mated_in(ply);
              return true;
          }
      }
  }

  return false;
}

// Position::chased() tests whether the last move was a chase.

Bitboard Position::chased() const {
  Bitboard b = 0;
  if (st->move == MOVE_NONE)
      return b;

  Bitboard pins = blockers_for_king(sideToMove);
      Bitboard kingFilePieces = file_bb(file_of(square<KING>(~sideToMove))) & pieces(sideToMove);
      if ((kingFilePieces & pieces(sideToMove, KING)) && !more_than_one(kingFilePieces & ~pieces(KING)))
          pins |= kingFilePieces & ~pieces(KING);
  auto addChased = [&](Square attackerSq, PieceType attackerType, Bitboard attacks) {
      if (attacks & ~b)
      {
          // Exclude attacks on unpromoted soldiers and checks
          attacks &= ~(pieces(sideToMove, KING, SOLDIER) ^ promoted_soldiers(sideToMove));
          // Attacks against stronger pieces
          if (attackerType == HORSE || attackerType == CANNON)
              b |= attacks & pieces(sideToMove, ROOK);
          if (attackerType == ELEPHANT || attackerType == FERS)
              b |= attacks & pieces(sideToMove, ROOK, CANNON, HORSE);
          // Exclude mutual/symmetric attacks
          // Exceptions:
          // - asymmetric pieces ("impaired horse")
          // - pins
          if (attackerType == HORSE && (PseudoAttacks[WHITE][FERS][attackerSq] & pieces()))
          {
              Bitboard horses = attacks & pieces(sideToMove, attackerType);
              while (horses)
              {
                  Square s = pop_lsb(horses);
                  if (attacks_bb(sideToMove, attackerType, s, pieces()) & attackerSq)
                      attacks ^= s;
              }
          }
          else
              attacks &= ~pieces(sideToMove, attackerType) | pins;
          // Attacks against potentially unprotected pieces
          while (attacks)
          {
              Square s = pop_lsb(attacks);
              Bitboard roots = attackers_to(s, pieces() ^ attackerSq, sideToMove) & ~pins;
              if (!roots || (roots == pieces(sideToMove, KING) && (attacks_bb(sideToMove, ROOK, square<KING>(~sideToMove), pieces() ^ attackerSq) & s)))
                  b |= s;
          }
      }
  };

  // Direct attacks
  Square from = from_sq(st->move);
  Square to = to_sq(st->move);
  PieceType movedPiece = type_of(piece_on(to));
  if (movedPiece != KING && movedPiece != SOLDIER)
  {
      Bitboard directAttacks = attacks_from(~sideToMove, movedPiece, to) & pieces(sideToMove);
      // Only new attacks count. This avoids expensive comparison of previous and new attacks.
      if (movedPiece == ROOK || movedPiece == CANNON)
          directAttacks &= ~line_bb(from, to);
      addChased(to, movedPiece, directAttacks);
  }

  // Discovered attacks
  Bitboard discoveryCandidates =  (PseudoAttacks[WHITE][WAZIR][from] & pieces(~sideToMove, HORSE))
                                | (PseudoAttacks[WHITE][FERS][from] & pieces(~sideToMove, ELEPHANT))
                                | (PseudoAttacks[WHITE][ROOK][from] & pieces(~sideToMove, CANNON, ROOK))
                                | (PseudoAttacks[WHITE][ROOK][to] & pieces(~sideToMove, CANNON));
  while (discoveryCandidates)
  {
      Square s = pop_lsb(discoveryCandidates);
      PieceType discoveryPiece = type_of(piece_on(s));
      Bitboard discoveries =   pieces(sideToMove)
                            &  attacks_bb(~sideToMove, discoveryPiece, s, pieces())
                            & ~attacks_bb(~sideToMove, discoveryPiece, s, (captured_piece() ? pieces() : pieces() ^ to) ^ from);
      addChased(s, discoveryPiece, discoveries);
  }

  // Changes in real roots and discovered checks
  if (st->pliesFromNull > 0)
  {
      // Fake roots
      Bitboard newPins = st->blockersForKing[sideToMove] & ~st->previous->blockersForKing[sideToMove] & pieces(sideToMove);
      while (newPins)
      {
          Square s = pop_lsb(newPins);
          PieceType pinnedPiece = type_of(piece_on(s));
          Bitboard fakeRooted =  pieces(sideToMove)
                               & ~(pieces(sideToMove, KING, SOLDIER) ^ promoted_soldiers(sideToMove))
                               & attacks_bb(sideToMove, pinnedPiece, s, pieces());
          while (fakeRooted)
          {
              Square s2 = pop_lsb(fakeRooted);
              if (attackers_to(s2, ~sideToMove) & ~blockers_for_king(~sideToMove))
                  b |= s2;
          }
      }
      // Discovered checks
      Bitboard newDiscoverers = st->blockersForKing[sideToMove] & ~st->previous->blockersForKing[sideToMove] & pieces(~sideToMove);
      while (newDiscoverers)
      {
          Square s = pop_lsb(newDiscoverers);
          PieceType discoveryPiece = type_of(piece_on(s));
          Bitboard discoveryAttacks = attacks_from(~sideToMove, discoveryPiece, s) & pieces(sideToMove);
          // Include all captures except where the king can pseudo-legally recapture
          b |= discoveryAttacks & ~attacks_from(sideToMove, KING, square<KING>(sideToMove));
          // Include captures where king can not legally recapture
          discoveryAttacks &= attacks_from(sideToMove, KING, square<KING>(sideToMove));
          while (discoveryAttacks)
          {
              Square s2 = pop_lsb(discoveryAttacks);
              if (attackers_to(s2, pieces() ^ s ^ square<KING>(sideToMove), ~sideToMove) & ~square_bb(s))
                  b |= s2;
          }
      }
  }

  return b;
}

// Position::has_repeated() tests whether there has been at least one repetition
// of positions since the last capture or pawn move.

bool Position::has_repeated() const {

    StateInfo* stc = st;
    int end = std::min(st->rule50, st->pliesFromNull);
    while (end-- >= 4)
    {
        if (stc->repetition)
            return true;

        stc = stc->previous;
    }
    return false;
}


/// Position::has_game_cycle() tests if the position has a move which draws by repetition,
/// or an earlier position has a move that directly reaches the current position.

bool Position::has_game_cycle(int ply) const {

  int j;

  int end = std::min(st->rule50, st->pliesFromNull);

  if (end < 3 || var->nFoldValue != VALUE_DRAW || var->perpetualCheckIllegal || var->materialCounting || var->moveRepetitionIllegal)
    return false;

  Key originalKey = st->key;
  StateInfo* stp = st->previous;

  for (int i = 3; i <= end; i += 2)
  {
      stp = stp->previous->previous;

      Key moveKey = originalKey ^ stp->key;
      if (   (j = H1(moveKey), cuckoo[j] == moveKey)
          || (j = H2(moveKey), cuckoo[j] == moveKey))
      {
          Move move = cuckooMove[j];
          Square s1 = from_sq(move);
          Square s2 = to_sq(move);

          if (!((between_bb(s1, s2) ^ s2) & pieces()))
          {
              if (ply > i)
                  return true;

              // For nodes before or at the root, check that the move is a
              // repetition rather than a move to the current position.
              // In the cuckoo table, both moves Rc1c5 and Rc5c1 are stored in
              // the same location, so we have to select which square to check.
              if (color_of(piece_on(empty(s1) ? s2 : s1)) != side_to_move())
                  continue;

              // For repetitions before or at the root, require one more
              if (stp->repetition)
                  return true;
          }
      }
  }
  return false;
}


/// Position::counting_limit() returns the counting limit in full moves.

int Position::counting_limit() const {
  return 0;
}


/// Position::flip() flips position with the white and black sides reversed. This
/// is only useful for debugging e.g. for finding evaluation symmetry bugs.

void Position::flip() {

  string f, token;
  std::stringstream ss(fen());

  for (Rank r = max_rank(); r >= RANK_1; --r) // Piece placement
  {
      std::getline(ss, token, r > RANK_1 ? '/' : ' ');
      f.insert(0, token + (f.empty() ? " " : "/"));
  }

  ss >> token; // Active color
  f += (token == "w" ? "B " : "W "); // Will be lowercased later

  ss >> token; // Castling availability
  f += token + " ";

  std::transform(f.begin(), f.end(), f.begin(),
                 [](char c) { return char(islower(c) ? toupper(c) : tolower(c)); });

  ss >> token; // En passant square
  f += (token == "-" ? token : token.replace(1, 1, token[1] == '3' ? "6" : "3"));

  std::getline(ss, token); // Half and full moves
  f += token;

  set(variant(), f, st, this_thread());

  assert(pos_is_ok());
}


/// Position::pos_is_ok() performs some consistency checks for the
/// position object and raises an asserts if something wrong is detected.
/// This is meant to be helpful when debugging.

bool Position::pos_is_ok() const {

  constexpr bool Fast = true; // Quick (default) or full check?

  if (   (sideToMove != WHITE && sideToMove != BLACK)
      || (count<KING>(WHITE) && piece_on(square<KING>(WHITE)) != make_piece(WHITE, KING))
      || (count<KING>(BLACK) && piece_on(square<KING>(BLACK)) != make_piece(BLACK, KING))
      || (   ep_square() != SQ_NONE
          && relative_rank(~sideToMove, ep_square(), max_rank()) > Rank(double_step_rank_max() + 1)))
      assert(0 && "pos_is_ok: Default");

  if (Fast)
      return true;

  if (   pieceCount[make_piece(~sideToMove, KING)]
      && (attackers_to(square<KING>(~sideToMove)) & pieces(sideToMove)))
      assert(0 && "pos_is_ok: Kings");

  if (   pieceCount[make_piece(WHITE, PAWN)] > 64
      || pieceCount[make_piece(BLACK, PAWN)] > 64)
      assert(0 && "pos_is_ok: Pawns");

  if (   (pieces(WHITE) & pieces(BLACK))
      || (pieces(WHITE) | pieces(BLACK)) != pieces()
      || popcount(pieces(WHITE)) > 64
      || popcount(pieces(BLACK)) > 64)
      assert(0 && "pos_is_ok: Bitboards");

  for (PieceType p1 = PAWN; p1 <= KING; ++p1)
      for (PieceType p2 = PAWN; p2 <= KING; ++p2)
          if (p1 != p2 && (pieces(p1) & pieces(p2)))
              assert(0 && "pos_is_ok: Bitboards");

  StateInfo si = *st;
  ASSERT_ALIGNED(&si, Eval::NNUE::CacheLineSize);

  set_state(&si);
  if (std::memcmp(&si, st, sizeof(StateInfo)))
      assert(0 && "pos_is_ok: State");

  for (Color c : {WHITE, BLACK})
      for (PieceType pt = PAWN; pt <= KING; ++pt)
      {
          Piece pc = make_piece(c, pt);
          if (   pieceCount[pc] != popcount(pieces(c, pt))
              || pieceCount[pc] != std::count(board, board + SQUARE_NB, pc))
              assert(0 && "pos_is_ok: Pieces");
      }

  for (Color c : { WHITE, BLACK })
      for (CastlingRights cr : {c & KING_SIDE, c & QUEEN_SIDE})
      {
          if (!can_castle(cr))
              continue;

          if (   piece_on(castlingRookSquare[cr]) != make_piece(c, castling_rook_piece())
              || castlingRightsMask[castlingRookSquare[cr]] != cr
              || (count<KING>(c) && (castlingRightsMask[square<KING>(c)] & cr) != cr))
              assert(0 && "pos_is_ok: Castling");
      }

  return true;
}

// Add a function that directly unpacks for speed. It's pretty tough.
// Write it by combining packer::unpack() and Position::set().
// If there is a problem with the passed phase and there is an error, non-zero is returned.
int Position::set_from_packed_sfen(const Tools::PackedSfen& sfen , StateInfo* si, Thread* th)
{
  return Tools::set_from_packed_sfen(*this, sfen, si, th);
}

// Get the packed sfen. Returns to the buffer specified in the argument.
void Position::sfen_pack(Tools::PackedSfen& sfen)
{
  sfen = Tools::sfen_pack(*this);
}

} // namespace Stockfish
