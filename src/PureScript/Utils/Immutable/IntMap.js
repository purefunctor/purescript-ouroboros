export function eqIntMapImpl(eq, xs, ys) {
    let keys = new Set([...xs.keys(), ...ys.keys()].sort((a, b) => a - b));

    let isEqual = xs.size === ys.size;
    if (!isEqual) {
        return isEqual;
    }
    for (const key of keys) {
        let hasX = xs.has(key);
        let hasY = ys.has(key);
        if (hasX && hasY) {
            isEqual &&= eq(xs.get(key), ys.get(key));
        } else {
            isEqual = false;
        }
    }
    return isEqual;
}

export function ordIntMapImpl(compareKey, compareValue, lt, eq, gt, append, xs, ys) {
    let xsKeys = [...xs.keys()];
    let ysKeys = [...ys.keys()];

    let ordering = eq;
    let maxIndex = Math.min(xsKeys.length, ysKeys.length);
    for (let index = 0; index < maxIndex; index++) {
        let xsKey = xsKeys[index];
        let ysKey = ysKeys[index];
        ordering = append(ordering, compareKey(xsKey, ysKey));
        let x = xs.get(xsKey);
        let y = ys.get(ysKey);
        ordering = append(ordering, compareValue(x, y));
    }

    if (xsKeys.length < ysKeys.length) {
        ordering = append(ordering, lt);
    } else if (xsKeys.length > ysKeys.length) {
        ordering = append(ordering, gt);
    }

    return ordering;
}

export function fromArrayImpl(fn, xs) {
    let result = new Map();
    for (const x of xs) {
        let { key, value } = fn(x);
        result.set(key, value);
    }
    return result;
}

export function toArrayImpl(fn, xs) {
    let result = [];
    for (const key of xs.keys()) {
        result.push(fn(key, xs.get(key)));
    }
    return result;
}

export function getImpl(just, nothing, k, m) {
  if (m.has(k)) {
    return just(m.get(k));
  } else {
    return nothing;
  }
}
