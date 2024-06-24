export function tarjanImpl(vertices, edges, onAcyclic, onCyclic) {
  let index = 0;
  let stack = [];

  let indices = [];
  let lowlinks = [];
  let onStack = [];

  function strongConnect(atKey) {
    indices[atKey] = index;
    lowlinks[atKey] = index;
    index += 1;
    stack.push(atKey);
    onStack[atKey] = true;

    for (const edgeKey of edges[atKey]) {
      if (indices[edgeKey] === undefined) {
        strongConnect(edgeKey);
        lowlinks[atKey] = Math.min(lowlinks[atKey], lowlinks[edgeKey]);
      } else if (onStack[edgeKey] === true) {
        lowlinks[atKey] = Math.min(lowlinks[atKey], lowlinks[edgeKey]);
      }
    }

    if (lowlinks[atKey] === indices[atKey]) {
      let stronglyConnectedComponents = [];

      let stackKey = stack.pop();
      if (stackKey !== undefined) {
        onStack[stackKey] = false;
        stronglyConnectedComponents.push(stackKey);
        while (stackKey !== atKey) {
          stackKey = stack.pop();
          onStack[stackKey] = false;
          stronglyConnectedComponents.push(stackKey);
        }
      }

      if (edges[atKey].length === 0) {
        onAcyclic(stronglyConnectedComponents[0]);
      } else {
        onCyclic(stronglyConnectedComponents);
      }
    }
  }

  for (const vertexKey of vertices.keys()) {
    if (indices[vertexKey] === undefined) {
      strongConnect(vertexKey);
    }
  }
}
