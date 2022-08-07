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

#include <cassert>

#include "movegen.h"
#include "position.h"

namespace Stockfish {

namespace {

  template<MoveType T>
  ExtMove* make_move_and_gating(const Position& pos, ExtMove* moveList, Color us, Square from, Square to) {
    *moveList++ = make<T>(from, to);
    return moveList;
  }

  template<Color Us, GenType Type>
  ExtMove* generate_drops(const Position& pos, ExtMove* moveList, PieceType pt, Bitboard b) {
    assert(Type != CAPTURES);
    // Do not generate virtual drops for perft and at root
    if (pos.can_drop(Us, pt) || (Type != NON_EVASIONS && pos.two_boards() && pos.allow_virtual_drop(Us, pt)))
    {
        // Restrict to valid target
        b &= pos.drop_region(Us, pt);

        // Add to move list
        if (pos.drop_promoted() && pos.promoted_piece_type(pt))
        {
            Bitboard b2 = b;
            if (Type == QUIET_CHECKS)
                b2 &= pos.check_squares(pos.promoted_piece_type(pt));
            while (b2)
                *moveList++ = make_drop(pop_lsb(b2), pt, pos.promoted_piece_type(pt));
        }
        if (Type == QUIET_CHECKS || !pos.can_drop(Us, pt))
            b &= pos.check_squares(pt);
        while (b)
            *moveList++ = make_drop(pop_lsb(b), pt, pt);
    }

    return moveList;
  }

  template<Color Us, GenType Type>
  ExtMove* generate_pawn_moves(const Position& pos, ExtMove* moveList, Bitboard target) {

    constexpr Color     Them     = ~Us;
    constexpr Direction Up       = pawn_push(Us);
    constexpr Direction Down     = -pawn_push(Us);
    constexpr Direction UpRight  = (Us == WHITE ? NORTH_EAST : SOUTH_WEST);
    constexpr Direction UpLeft   = (Us == WHITE ? NORTH_WEST : SOUTH_EAST);

    Bitboard TRank8BB = pos.sittuyin_promotion() ? Bitboard(0) : zone_bb(Us, pos.promotion_rank(), pos.max_rank());
    Bitboard TRank7BB = shift<Down>(TRank8BB);
    // Define squares a pawn can pass during a double step

    const Bitboard emptySquares = Type == QUIETS || Type == QUIET_CHECKS ? target : ~pos.pieces() & pos.board_bb();
    const Bitboard enemies      = Type == EVASIONS ? (pos.checkers() & pos.non_sliding_riders() ? pos.pieces(Them) : pos.checkers())
                                : Type == CAPTURES ? target : pos.pieces(Them);

    Bitboard pawnsNotOn7 = pos.pieces(Us, PAWN) & (pos.mandatory_pawn_promotion() ? ~TRank7BB : AllSquares);

    // Single and double pawn pushes, no promotions
    if (Type != CAPTURES)
    {
        Bitboard b1 = shift<Up>(pawnsNotOn7)   & emptySquares;

        if (Type == EVASIONS) // Consider only blocking squares
            b1 &= target;

        if (Type == QUIET_CHECKS && pos.count<KING>(Them))
        {
            // To make a quiet check, you either make a direct check by pushing a pawn
            // or push a blocker pawn that is not on the same file as the enemy king.
            // Discovered check promotion has been already generated amongst the captures.
            Square ksq = pos.square<KING>(Them);
            Bitboard dcCandidatePawns = pos.blockers_for_king(Them) & ~file_bb(ksq);
            b1 &= pawn_attacks_bb(Them, ksq) | shift<   Up>(dcCandidatePawns);
        }

        while (b1)
        {
            Square to = pop_lsb(b1);
            *moveList++ = make_move(to - Up, to);
        }
    }

    // Standard and en passant captures
    if (Type == CAPTURES || Type == EVASIONS || Type == NON_EVASIONS)
    {
        Bitboard b1 = shift<UpRight>(pawnsNotOn7) & enemies;
        Bitboard b2 = shift<UpLeft >(pawnsNotOn7) & enemies;

        while (b1)
        {
            Square to = pop_lsb(b1);
            *moveList++ = make_move(to - UpRight, to);
        }

        while (b2)
        {
            Square to = pop_lsb(b2);
            *moveList++ = make_move(to - UpLeft, to);
        }
    }

    return moveList;
  }


  template<Color Us, bool Checks>
  ExtMove* generate_moves(const Position& pos, ExtMove* moveList, PieceType Pt, Bitboard target) {

    assert(Pt != KING && Pt != PAWN);

    Bitboard bb = pos.pieces(Us, Pt);

    while (bb)
    {
        Square from = pop_lsb(bb);

        Bitboard b1 = (  (pos.attacks_from(Us, Pt, from) & pos.pieces())
                       | (pos.moves_from(Us, Pt, from) & ~pos.pieces())) & target;
        PieceType promPt = pos.promoted_piece_type(Pt);
        Bitboard b2 = promPt && (!pos.promotion_limit(promPt) || pos.promotion_limit(promPt) > pos.count(Us, promPt)) ? b1 : Bitboard(0);
        Bitboard b3 = pos.piece_demotion() && pos.is_promoted(from) ? b1 : Bitboard(0);

        // Restrict target squares considering promotion zone
        if (b2 | b3)
        {
            Bitboard promotion_zone = zone_bb(Us, pos.promotion_rank(), pos.max_rank());
            if (pos.mandatory_piece_promotion())
                b1 &= (promotion_zone & from ? Bitboard(0) : ~promotion_zone) | (pos.piece_promotion_on_capture() ? ~pos.pieces() : Bitboard(0));
            // Exclude quiet promotions/demotions
            if (pos.piece_promotion_on_capture())
            {
                b2 &= pos.pieces();
                b3 &= pos.pieces();
            }
            // Consider promotions/demotions into promotion zone
            if (!(promotion_zone & from))
            {
                b2 &= promotion_zone;
                b3 &= promotion_zone;
            }
        }

        if (Checks)
        {
            b1 &= pos.check_squares(Pt);
            if (b2)
                b2 &= pos.check_squares(pos.promoted_piece_type(Pt));
            if (b3)
                b3 &= pos.check_squares(type_of(pos.unpromoted_piece_on(from)));
        }

        while (b1)
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, from, pop_lsb(b1));
    }

    return moveList;
  }


  template<Color Us, GenType Type>
  ExtMove* generate_all(const Position& pos, ExtMove* moveList) {

    static_assert(Type != LEGAL, "Unsupported type in generate_all()");

    constexpr bool Checks = Type == QUIET_CHECKS; // Reduce template instantiations
    const Square ksq = pos.count<KING>(Us) ? pos.square<KING>(Us) : SQ_NONE;
    Bitboard target;

    // Skip generating non-king moves when in double check
    if (Type != EVASIONS || !more_than_one(pos.checkers() & ~pos.non_sliding_riders()))
    {
        target = Type == EVASIONS     ?  between_bb(ksq, lsb(pos.checkers()))
               : Type == NON_EVASIONS ? ~pos.pieces( Us)
               : Type == CAPTURES     ?  pos.pieces(~Us)
                                      : ~pos.pieces(   ); // QUIETS || QUIET_CHECKS

        if (Type == EVASIONS)
        {
            if (pos.checkers() & pos.non_sliding_riders())
                target = ~pos.pieces(Us);
            // Leaper attacks can not be blocked
            Square checksq = lsb(pos.checkers());
            if (LeaperAttacks[~Us][type_of(pos.piece_on(checksq))][checksq] & pos.square<KING>(Us))
                target = pos.checkers();
        }

        target &= pos.board_bb();

        moveList = generate_pawn_moves<Us, Type>(pos, moveList, target);
        for (PieceType pt : pos.piece_types())
            if (pt != PAWN && pt != KING)
                moveList = generate_moves<Us, Checks>(pos, moveList, pt, target);
        // generate drops
        if (pos.piece_drops() && Type != CAPTURES && (pos.can_drop(Us, ALL_PIECES)))
            for (PieceType pt : pos.piece_types())
                moveList = generate_drops<Us, Type>(pos, moveList, pt, target & ~pos.pieces(~Us));
    }

    // King moves
    if (pos.count<KING>(Us) && (!Checks || pos.blockers_for_king(~Us) & ksq))
    {
        Bitboard b = (  (pos.attacks_from(Us, KING, ksq) & pos.pieces())
                      | (pos.moves_from(Us, KING, ksq) & ~pos.pieces())) & (Type == EVASIONS ? ~pos.pieces(Us) : target);
        while (b)
            moveList = make_move_and_gating<NORMAL>(pos, moveList, Us, ksq, pop_lsb(b));
    }

    return moveList;
  }

} // namespace


/// <CAPTURES>     Generates all pseudo-legal captures plus queen promotions
/// <QUIETS>       Generates all pseudo-legal non-captures and underpromotions
/// <EVASIONS>     Generates all pseudo-legal check evasions when the side to move is in check
/// <QUIET_CHECKS> Generates all pseudo-legal non-captures giving check, except castling and promotions
/// <NON_EVASIONS> Generates all pseudo-legal captures and non-captures
///
/// Returns a pointer to the end of the move list.

template<GenType Type>
ExtMove* generate(const Position& pos, ExtMove* moveList) {

  static_assert(Type != LEGAL, "Unsupported type in generate()");
  assert((Type == EVASIONS) == (bool)pos.checkers());

  Color us = pos.side_to_move();

  return us == WHITE ? generate_all<WHITE, Type>(pos, moveList)
                     : generate_all<BLACK, Type>(pos, moveList);
}

// Explicit template instantiations
template ExtMove* generate<CAPTURES>(const Position&, ExtMove*);
template ExtMove* generate<QUIETS>(const Position&, ExtMove*);
template ExtMove* generate<EVASIONS>(const Position&, ExtMove*);
template ExtMove* generate<QUIET_CHECKS>(const Position&, ExtMove*);
template ExtMove* generate<NON_EVASIONS>(const Position&, ExtMove*);


/// generate<LEGAL> generates all the legal moves in the given position

template<>
ExtMove* generate<LEGAL>(const Position& pos, ExtMove* moveList) {

  if (pos.is_immediate_game_end())
      return moveList;

  ExtMove* cur = moveList;

  moveList = pos.checkers() ? generate<EVASIONS    >(pos, moveList)
                            : generate<NON_EVASIONS>(pos, moveList);
  while (cur != moveList)
      if (!pos.legal(*cur))
          *cur = (--moveList)->move;
      else
          ++cur;

  return moveList;
}

} // namespace Stockfish
