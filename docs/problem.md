# Problem statement and provenance

## The game

The current state is an odd positive integer `n`.

For `n > 1`, the player to move chooses one of

\[
3n+1,\qquad 3n-1,
\]

then divides the chosen number by `2` repeatedly until it is odd. If the resulting odd number is `1`, the player who made the move wins.

Players alternate and have perfect information.

## Problem

Prove that, under optimal play, every odd starting value leads to `1` after finitely many moves.

Repository status: **OPEN**. Sections 129–138 of `verified-results.md` give
proved local rank lemmas and a conditional global assembly, but the concrete
high-return token-provenance/lifecycle refinement has not been proved. The
current statement of the gap is in `high-return-provenance-obligation.md`;
`global-proof.md` is explicitly conditional on closing it.

Because arbitrary move sequences can cycle, this is not the ordinary Collatz convergence statement. For example,

\[
5\to7\to5
\]

is possible under suitable choices. The task is to rule out draw positions under optimal game-theoretic play.

## Prize

Ingo Althöfer offers €500 for a proof that every odd starting number reaches `1` when both players act optimally. The current official deadline is 31 December 2037.

Official page:

<https://althofer.de/collatz-prizes.html>

The game is called the `3n+-1 game` on that page and is stated there to have
been created in July 2023.  The mathematical rules, however, are not new:
they are exactly John Conway's **Beans-Don't-Talk** game, documented by
Richard K. Guy in 1986.  Guy's later 1996 problem survey explicitly asks
whether this game has any `O`-positions, his term for positions of infinite
remoteness.  Thus the prize question is a modern restatement of that older
open problem.

Historical references:

- R. K. Guy, *John Isbell's Game of Beanstalk and John Conway's Game of
  Beans-Don't-Talk*, Mathematics Magazine 59 (1986), 259--269,
  <https://doi.org/10.1080/0025570X.1986.11977258>.
- R. K. Guy, *Unsolved Problems in Combinatorial Games*, problem 42,
  Games of No Chance, MSRI Publications 29 (1996),
  <https://library.slmath.org/books/Book29/files/unsolved.pdf>.
- OEIS records several known finite-remoteness layers under the same game
  name; for example <https://oeis.org/A005698> gives remoteness two.  These
  layers do not settle whether every position has finite remoteness.

## Publication

I. Althöfer, M. Hartisch, T. Zipproth,
*Analysis of a Collatz Game and Other Variants of the 3n+1 Problem*,
Advances in Computer Games, 2024, pp. 123–132.
DOI: `10.1007/978-3-031-54968-7_11`.

## Outcome terminology used here

For the player to move:

- `LOSS`: the opponent can force a win;
- `WIN`: the player can force a win;
- `DRAW`: neither player can force a win, and optimal play can continue forever;
- `UNKNOWN`: a computational procedure has not proved the status.

`UNKNOWN` is not a mathematical outcome.
