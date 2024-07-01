export function tarjanImpl(internal, onAcyclic, onCyclic) {
  let index = 0;
  let stack = [];
  let indices = new Map();
  let lowlinks = new Map();
  let onStack = new Map();

  function strongConnect(atKey) {
    indices.set(atKey, index);
    lowlinks.set(atKey, index);
    index += 1;
    stack.push(atKey);
    onStack.set(atKey, true);

    const edges = internal.get(atKey)["edges"];
    for (const edgeKey of edges.keys()) {
      if (indices.get(edgeKey) === undefined) {
        strongConnect(edgeKey);
        lowlinks.set(atKey, Math.min(lowlinks.get(atKey), lowlinks.get(edgeKey)));
      } else if (onStack.get(edgeKey) === true) {
        lowlinks.set(atKey, Math.min(lowlinks.get(atKey), lowlinks.get(edgeKey)));
      }
    }

    if (lowlinks.get(atKey) === indices.get(atKey)) {
      let stronglyConnectedComponents = [];

      let stackKey = stack.pop();
      if (stackKey !== undefined) {
        onStack.set(stackKey, false);
        stronglyConnectedComponents.push(stackKey);
        while (stackKey !== atKey) {
          stackKey = stack.pop();
          onStack.set(stackKey, false);
          stronglyConnectedComponents.push(stackKey);
        }
      }

      if (stronglyConnectedComponents.length === 1) {
        if (edges.has(atKey)) {
          onCyclic(stronglyConnectedComponents);
        } else {
          onAcyclic(stronglyConnectedComponents[0]);
        }
      } else {
        onCyclic(stronglyConnectedComponents);
      }
    }
  }

  for (const atKey of internal.keys()) {
    if (indices.get(atKey) === undefined) {
      strongConnect(atKey);
    }
  }
}
