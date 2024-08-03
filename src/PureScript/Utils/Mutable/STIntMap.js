export function empty() {
    return new Map();
}

export function setImpl(k, v, m) {
  m.set(k, v);
}

export function getImpl(just, nothing, k, m) {
  if (m.has(k)) {
    return just(m.get(k));
  } else {
    return nothing;
  }
}

export function hasImpl(k, m) {
  return m.has(k);
}

export function deleteImpl(k, m) {
  m.delete(k);
}

export function clearImpl(m) {
  m.clear();
}

export function freezeImpl(m) {
  return new Map(m);
}
