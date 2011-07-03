#!/usr/bin/python

# Problem:
#
# Solve the sliding tile puzzle below by rearranging the pieces until red 
# piece to the goal (Middle of the opposite right side). 
# Each piece can slide Up, Down, Left and Right into the unoccupied holes.
#
#
# (Start)              (r at Goal, others probably not valid for this layout)
#
#  w1 w1 g1 g2 _1      w1 w1 g1 g2 _1
#   r  r w2 w3 w4      w2 w3 w4  r  r 
#   r  r w2 w3 w4      w2 w3 w4  r  r 
#  w5 w5 g3 g4 _2      w5 w5 g3 g4 _2
#


# Attack:
#   Use brute force breadth-first search.
#   Try moving every piece in every direction around the two holes each 
#   iteration.
#   Reject any board layout we have seen before.
#   Accept any board if the red square is on the other side (goal).
#


# Addendum:
#   Depth-first search: ~ 10s, but this solution has 110472 moves.
#                       Recording the actual moves isn't doable as the memory
#                       required quickly grows to many 10s of gigabytes 
#                       before running out of RAM.
#
#   Breadth-first search: 30min (2.8GHz Core i7), max ~4.3Gb memory
#                         138 moves (*should* be guaranteed shortest due to BFS)
#
#                         g4 w2 w4 _2 _1 
#                         g1 w2 w4 r  r  
#                         w1 w1 w3 r  r  
#                         w5 w5 w3 g3 g2 
#                         
#   cProfile showed main bottleneck was multiple redundant piece_locations()
#   calls, replaced with cache version. Rest of code is evenly matched.
#   Could be made faster by getting rid of stuff like set operations,
#   and lower mem usage by replacing piece strings and movement
#   directions with indexes to a table -- but thats extra work.
#
#   For (similar) 15puzzle solvers, Iterative Deepening Depth-First Search has
#   been suggested as a faster algorithm than BFS.
#

# Addendum 2:
#
#   Recording 2 space moves as one results in 113 move solution in ~24min.
#
#   This puzzle is called 'Klotski', and the minimum number of moves to finish
#   from the 'standard' starting layout is 81 (counting 2 space moves as 1),
#   but I haven't tested it with this program. Some solvers out there are pretty
#   fast (~ sec).
#
#   Reducing each board to a single string before adding to the 'seen' set
#   dramatically reduces memory, but makes the code run ~1.25 times slower.
#
#
#   Looking at a fast solver http://www.treskal.com/kalle/klotski.pdf 
#   (Karl Wiberg), surprised to see it only uses a plain brute force search.
#   *But*, for previously seen board layouts, it only records the types of 
#   pieces ('w') at each position, not piece identity ('w2').
#
#   ==> Discard equivilant layouts by passing the current board through
#   'baseform(board)' before checking. (baseform() relabels each similar piece
#   in ascending order). Number of layouts searched is greatly reduced
#   from e.g.:
#       ~7665014 (4GB, ~30min)
#   to:
#          26383 (15M, ~7 sec).
#   ... done.
#


import collections
import os, sys
from commands import getoutput

#               [0][0]
start_board = (( 'w1', 'w1', 'g1', 'g2', '_1' ),
               (  'r',  'r', 'w2', 'w3', 'w4' ),
               (  'r',  'r', 'w2', 'w3', 'w4' ),
               ( 'w5', 'w5', 'g3', 'g4', '_2' ))
#                                        [3][4]

#start_board = (( 'w1', 'w1', 'g1',  'r',  'r' ),
#               ( 'w2', 'w3', 'w4',  'r',  'r' ),
#               ( 'w2', 'w3', 'w4', 'g2', '_1' ),
#               ( 'w5', 'w5', 'g3', 'g4', '_2' ))
#
#moves = [('g2', 0, 1), ('g2', 1, 0), ('r', 1, 0)]


def piece_locations(board):
    pos = {}
    for x in range(len(board)):
        for y in range(len(board[0])):
            pos.setdefault(board[x][y], []).append((x,y))
    return pos


def move_piece(board, (piece, dx, dy), loc_cache=None):
    displaced = set()
    new_board = map(list, board)
    old_loc = piece_locations(board)[piece] if not loc_cache else loc_cache
    for x,y in old_loc:
        if board[x+dx][y+dy] not in ('_1', '_2', piece):
            return None
        displaced.add(board[x+dx][y+dy])
        new_board[x+dx][y+dy] = board[x][y]
    holes = displaced - set([piece])
    new_loc = [(x+dx, y+dy) for x,y in old_loc]
    for x,y in set(old_loc) - set(new_loc):
        new_board[x][y] = holes.pop()
    return tuple(map(tuple, new_board))


def possible_moves(board):
    p_locations = piece_locations(board)
    for hx,hy in (p_locations['_1'][0], p_locations['_2'][0]):
        for dx,dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            if 0 <= hx+dx < len(board) and 0 <= hy+dy < len(board[0]):
                piece = board[hx+dx][hy+dy]
                nboard = move_piece(board, (piece, -dx,-dy), p_locations[piece])
                if nboard:
                    yield (nboard, (piece, -dx, -dy))
    return


def baseform(board):
    def uniq_ordered(seq):    # src: Dave Kirby (via Peter Bengtsson)
        seen = set()
        return [x for x in seq if x not in seen and not seen.add(x)]
    pieces = uniq_ordered(piece for row in board for piece in row)
    pgroups = {}
    for piece in pieces:
        pgroups.setdefault(piece[0], []).append(piece)
    pmap = dict(m for p in pgroups for m in zip(pgroups[p], sorted(pgroups[p])))
    return tuple(map(tuple, [[pmap[piece] for piece in row] for row in board]))


def accept(board):
    return board[1][3] == board[1][4] == board[2][3] == board[2][4] == 'r'


def search(board):
    seen = set()
    worklist = collections.deque([(board, [])])
#    i = 0
    while len(worklist) > 0:
#        if i % 100000 == 0:
#            print getoutput('ps -o "%mem vsz rss time" -p '+str(os.getpid()))
#            print len(worklist), len(seen), len(worklist[0][1])
#            print_board(worklist[0][0])
#            sys.stdout.flush()
#        i += 1
        kboard, kmoves = worklist.popleft()
        for nboard, nmove in possible_moves(kboard):
            bfnboard = baseform(nboard)
            if bfnboard not in seen:
                if accept(nboard):
                    print 'Found solution, moves:', len(kmoves)+1, 'layouts explored:', len(seen)
                    return nboard, kmoves+[nmove]
                seen.add(bfnboard)
                if kmoves and kmoves[-1] == nmove:
                    nmove2 = tuple([nmove[0], 2*nmove[1], 2*nmove[2]])
                    worklist.appendleft((nboard, kmoves[:-1]+[nmove2]))
                else:
                    worklist.append((nboard, kmoves+[nmove]))        # Breadth-first search
                    #worklist.appendleft((nboard, kmoves+[nmove]))   # Depth-first search
                    #worklist.appendleft((nboard, []))  # Depth-first search (dont record moves)
    return None


def print_board(board):
    for line in board:
        for piece in line:
            print piece.ljust(2),
        print '\n',
    print '\n',
    return


if __name__ == '__main__':
    print_board(start_board)
    final_board, moves = search(start_board)
    print_board(final_board)
    print len(moves), moves
