#!/usr/bin/env node
"use strict";

// Exploratory finite constraint propagation for the marked frame in
// Sections 56--57. A survivor is only an unverified lead; rejection at a
// fixed depth is not a proof of the infinite theorem.

const DRAW = 1;
const WIN = 2;
const LOSS = 4;
const ALL = DRAW | WIN | LOSS;
const TRACE = process.argv.includes("trace");

function A(q) {
  return Math.floor((3 * q + 1) / 2);
}

function alternatingRemainder(value) {
  if (value === 0) return 0;
  const original = value;
  let previous = value % 2;
  let divisor = 1;
  while (value > 0) {
    divisor *= 2;
    value = Math.floor(value / 2);
    if (value === 0 || value % 2 === previous) break;
    previous = 1 - previous;
  }
  return Math.floor(original / divisor);
}

function B(q) {
  return alternatingRemainder(A(q));
}

function alpha(q) {
  return 1 - (Math.floor(q / 2) % 2);
}

function embeddedOriginalState(q) {
  return 2 * A(q) + 1;
}

function tailState(coefficient, exponent, tail) {
  return coefficient * 2 ** exponent - tail;
}

function coefficientSource(state) {
  if (state === 0) return 0;
  const tail = state % 2;
  let coefficient = tail === 0 ? state : state + 1;
  while (coefficient % 2 === 0) coefficient /= 2;
  while (coefficient % 3 === 0) coefficient /= 3;
  const image = (coefficient - 1) / 2;
  if (image % 3 === 0) return (2 * image) / 3;
  if (image % 3 === 2) return (2 * image - 1) / 3;
  throw new Error("invalid embedded source");
}

const allowed = [];
for (const parent of [DRAW, WIN, LOSS]) {
  for (const first of [DRAW, WIN, LOSS]) {
    for (const second of [DRAW, WIN, LOSS]) {
      const valid =
        parent === LOSS
          ? first === WIN && second === WIN
          : parent === WIN
            ? first === LOSS || second === LOSS
            : first !== LOSS &&
              second !== LOSS &&
              (first === DRAW || second === DRAW);
      if (valid) allowed.push([parent, first, second]);
    }
  }
}

function markedConfiguration(
  b,
  lossIndex,
  drawIndex,
  tOutcome = WIN | LOSS,
  yOutcome = WIN | LOSS,
) {
  const w = A(b);
  const t = A(w);
  const z = B(b);
  const q = B(w);
  const y = A(q);
  const phase = alpha(t);
  const coefficient = embeddedOriginalState(y);
  const upper = tailState(coefficient, 3, phase);
  const lower = tailState(coefficient, 2, phase);
  const qChildren = [A(q), B(q)];
  if (process.argv.includes("loss-source")) {
    const sourceChildren = [A(y), B(y)];
    const canonicalLoss = [A(sourceChildren[0]), B(sourceChildren[0])][
      lossIndex
    ];
    return {
      roots: [
        b,
        w,
        t,
        z,
        q,
        y,
        upper,
        lower,
        ...sourceChildren,
        canonicalLoss,
        A(canonicalLoss),
        B(canonicalLoss),
      ],
      forced: [
        [b, WIN],
        [t, tOutcome],
        [q, WIN],
        [y, LOSS],
        [canonicalLoss, LOSS],
        [[upper, lower][drawIndex], DRAW],
      ],
      barrierWins: new Set(),
      forbiddenSources: new Set([
        ...sourceChildren,
        A(canonicalLoss),
        B(canonicalLoss),
      ]),
    };
  }
  return {
    roots: [b, w, t, z, q, y, upper, lower, qChildren[lossIndex]],
    forced: [
      [b, WIN],
      [t, tOutcome],
      [q, WIN],
      [y, yOutcome],
      [qChildren[lossIndex], LOSS],
      [[upper, lower][drawIndex], DRAW],
    ],
    barrierWins: new Set([
      q,
      A(qChildren[lossIndex]),
      B(qChildren[lossIndex]),
    ]),
    forbiddenSources: new Set(),
  };
}

function buildNeighbourhood(roots, depth) {
  const index = new Map();
  const values = [];
  function intern(value) {
    const known = index.get(value);
    if (known !== undefined) return known;
    const result = values.length;
    index.set(value, result);
    values.push(value);
    return result;
  }

  let frontier = [...new Set(roots)];
  for (const value of frontier) intern(value);
  const expanded = new Set();
  const parents = [];
  const firstChildren = [];
  const secondChildren = [];

  for (let level = 0; level < depth; level += 1) {
    const following = new Set();
    for (const parentValue of frontier) {
      if (parentValue === 0 || expanded.has(parentValue)) continue;
      const firstValue = A(parentValue);
      const secondValue = B(parentValue);
      parents.push(intern(parentValue));
      firstChildren.push(intern(firstValue));
      secondChildren.push(intern(secondValue));
      expanded.add(parentValue);
      following.add(firstValue);
      following.add(secondValue);
    }
    frontier = [...following];
  }

  return { index, values, parents, firstChildren, secondChildren };
}

function force(domains, node, outcome) {
  const narrowed = domains[node] & outcome;
  domains[node] = narrowed;
  return narrowed !== 0;
}

function propagate(graph, specification) {
  const { index, values, parents, firstChildren, secondChildren } = graph;
  const domains = new Uint8Array(values.length);
  const reasons = new Array(values.length);
  function explain(node, depth, seen = new Set()) {
    const value = values[node];
    const result = {
      value,
      domain: domains[node],
      reason: reasons[node],
    };
    if (depth === 0 || seen.has(node)) return result;
    const reason = reasons[node];
    if (reason?.kind !== "constraint") return result;
    const followingSeen = new Set(seen);
    followingSeen.add(node);
    result.dependencies = [reason.parent, ...reason.children]
      .filter((entry) => entry !== value)
      .map((entry) => explain(index.get(entry), depth - 1, followingSeen));
    return result;
  }
  domains.fill(ALL);
  const terminal = index.get(0);
  if (terminal !== undefined) {
    domains[terminal] = LOSS;
    reasons[terminal] = { kind: "terminal" };
  }

  for (let node = 0; node < values.length; node += 1) {
    if (specification.forbiddenSources.has(coefficientSource(values[node]))) {
      domains[node] &= ~DRAW;
      reasons[node] = {
        kind: "forbidden-source",
        source: coefficientSource(values[node]),
      };
    }
  }

  for (const [value, outcome] of specification.forced) {
    if (!force(domains, index.get(value), outcome)) {
      if (TRACE) {
        process.stderr.write(
          JSON.stringify({ kind: "forced-conflict", value, outcome }) + "\n",
        );
      }
      return false;
    }
    reasons[index.get(value)] = { kind: "forced", outcome };
  }

  const incidence = Array.from({ length: values.length }, () => []);
  for (let constraint = 0; constraint < parents.length; constraint += 1) {
    incidence[parents[constraint]].push(constraint);
    incidence[firstChildren[constraint]].push(constraint);
    incidence[secondChildren[constraint]].push(constraint);
    if (
      specification.barrierWins.has(values[firstChildren[constraint]]) ||
      specification.barrierWins.has(values[secondChildren[constraint]])
    ) {
      const parent = parents[constraint];
      domains[parent] &= ~DRAW;
      reasons[parent] = {
        kind: "barrier",
        children: [
          values[firstChildren[constraint]],
          values[secondChildren[constraint]],
        ],
      };
      if (domains[parent] === 0) {
        if (TRACE) {
          process.stderr.write(
            JSON.stringify({
              kind: "barrier-conflict",
              parent: values[parent],
              children: [
                values[firstChildren[constraint]],
                values[secondChildren[constraint]],
              ],
            }) + "\n",
          );
        }
        return false;
      }
    }
  }

  const queued = new Uint8Array(parents.length);
  const queue = [];
  for (let constraint = 0; constraint < parents.length; constraint += 1) {
    queue.push(constraint);
    queued[constraint] = 1;
  }

  for (let cursor = 0; cursor < queue.length; cursor += 1) {
    const constraint = queue[cursor];
    queued[constraint] = 0;
    const nodes = [
      parents[constraint],
      firstChildren[constraint],
      secondChildren[constraint],
    ];
    const masks = nodes.map((node) => domains[node]);
    const support = [0, 0, 0];
    for (const triple of allowed) {
      if (
        (masks[0] & triple[0]) !== 0 &&
        (masks[1] & triple[1]) !== 0 &&
        (masks[2] & triple[2]) !== 0
      ) {
        support[0] |= triple[0];
        support[1] |= triple[1];
        support[2] |= triple[2];
      }
    }

    for (let position = 0; position < 3; position += 1) {
      const node = nodes[position];
      const narrowed = domains[node] & support[position];
      if (narrowed === 0) {
        if (TRACE) {
          process.stderr.write(
            JSON.stringify({
              kind: "unsupported",
              parent: values[parents[constraint]],
              children: [
                values[firstChildren[constraint]],
                values[secondChildren[constraint]],
              ],
              masks,
              support,
              position,
              current: domains[node],
              reasons: nodes.map((entry) => reasons[entry]),
              explanation: nodes.map((entry) => explain(entry, 8)),
            }) + "\n",
          );
        }
        return false;
      }
      if (narrowed === domains[node]) continue;
      const previous = domains[node];
      domains[node] = narrowed;
      reasons[node] = {
        kind: "constraint",
        parent: values[parents[constraint]],
        children: [
          values[firstChildren[constraint]],
          values[secondChildren[constraint]],
        ],
        masks,
        support,
        position,
        previous,
        narrowed,
      };
      for (const adjacent of incidence[node]) {
        if (queued[adjacent] === 0) {
          queued[adjacent] = 1;
          queue.push(adjacent);
        }
      }
    }
  }
  return true;
}

function survives(configuration, depth) {
  const specification = markedConfiguration(...configuration);
  const graph = buildNeighbourhood(specification.roots, depth);
  return {
    consistent: propagate(graph, specification),
    nodes: graph.values.length,
  };
}

function main() {
  const maximum = Number(process.argv[2] ?? 4096);
  const depths = (process.argv[3] ?? "12,18,24,32")
    .split(",")
    .map(Number);
  const splitFiniteOutcomes =
    process.argv[4] === "split" || process.argv[5] === "split";
  let configurations;
  if (
    process.argv[4] !== undefined &&
    !["split", "loss-source"].includes(process.argv[4])
  ) {
    configurations = JSON.parse(process.argv[4]);
  } else {
    configurations = [];
    for (let b = 4; b < maximum; b += 1) {
      if (![4, 25, 38, 59].includes(b % 64)) continue;
      for (const lossIndex of [0, 1]) {
        for (const drawIndex of [0, 1]) {
          if (splitFiniteOutcomes) {
            for (const tOutcome of [WIN, LOSS]) {
              for (const yOutcome of [WIN, LOSS]) {
                configurations.push([
                  b,
                  lossIndex,
                  drawIndex,
                  tOutcome,
                  yOutcome,
                ]);
              }
            }
          } else {
            configurations.push([b, lossIndex, drawIndex]);
          }
        }
      }
    }
  }

  console.log("start " + configurations.length);
  for (const depth of depths) {
    const started = Date.now();
    let largest = 0;
    const following = [];
    for (const configuration of configurations) {
      const result = survives(configuration, depth);
      largest = Math.max(largest, result.nodes);
      if (result.consistent) following.push(configuration);
    }
    configurations = following;
    const elapsed = ((Date.now() - started) / 1000).toFixed(1);
    const rss = (process.memoryUsage().rss / 2 ** 20).toFixed(1);
    console.log(
      "depth " +
        depth +
        ": survivors " +
        configurations.length +
        "; largest graph " +
        largest +
        "; " +
        elapsed +
        "s; rss " +
        rss +
        " MiB",
    );
    console.log("first " + JSON.stringify(configurations.slice(0, 40)));
    if (configurations.length === 0) break;
  }
}

main();
