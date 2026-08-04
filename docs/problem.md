# Problem statement and provenance

## The game

The current state is an odd positive integer `n`.

For `n > 1`, the player to move chooses one of

\[
3n+1,\qquad 3n-1,
\]

then divides the chosen number by `2` repeatedly until it is odd. If the resulting odd number is `1`, the player who made the move wins.

Players alternate and have perfect information.

## Open problem

Prove that, under optimal play, every odd starting value leads to `1` after finitely many moves.

Because arbitrary move sequences can cycle, this is not the ordinary Collatz convergence statement. For example,

\[
5\to7\to5
\]

is possible under suitable choices. The task is to rule out draw positions under optimal game-theoretic play.

## Prize

Ingo Althöfer offers €500 for a proof that every odd starting number reaches `1` when both players act optimally. The current official deadline is 31 December 2037.

Official page:

<https://althofer.de/collatz-prizes.html>

The game is called the `3n+-1 game` on that page and is stated to have been created in July 2023.

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
