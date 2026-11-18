"""Verify the finite rule lists, independently of the all-size argument."""

from collections import deque


def output(rule, left, center, right):
    return (rule >> (4 * left + 2 * center + right)) & 1


def missing_word(rule):
    queue = deque([(frozenset(range(4)), "")])
    visited = {queue[0][0]}
    while queue:
        states, word = queue.popleft()
        if not states:
            return word
        for label in range(2):
            next_states = frozenset(
                (2 * (state & 1) + right)
                for state in states
                for right in range(2)
                if output(rule, state >> 1, state & 1, right) == label
            )
            if next_states not in visited:
                visited.add(next_states)
                queue.append((next_states, word + str(label)))
    return None


def main():
    left, right, affine, missing = set(), set(), set(), {}
    for rule in range(256):
        values = [output(rule, i >> 2, (i >> 1) & 1, i & 1) for i in range(8)]
        constant = values[0]
        linear = [values[i] ^ constant for i in (1, 2, 4)]
        is_affine = all(
            values[i] == (constant ^ ((i & 1) * linear[0])
                          ^ (((i >> 1) & 1) * linear[1]) ^ ((i >> 2) * linear[2]))
            for i in range(8)
        )
        if is_affine and any(linear):
            affine.add(rule)
        if not is_affine and all(values[i] != values[i + 4] for i in range(4)):
            left.add(rule)
        if not is_affine and all(values[i] != values[i + 1] for i in range(0, 8, 2)):
            right.add(rule)
        word = missing_word(rule)
        if word is not None:
            missing[rule] = word
    assert left == {30, 45, 75, 120, 135, 180, 210, 225}
    assert right == {86, 89, 101, 106, 149, 154, 166, 169}
    assert not left & right
    assert len(affine) == 14
    assert set(range(256)) - missing.keys() == affine | left | right
    assert max(map(len, missing.values())) == 9
    for rule in (37, 91, 164, 218):
        print(f"rule {rule}: missing word {missing[rule]}")
    print(f"all 256 checked; {len(left | right)} obstructed, {len(affine | missing.keys())} positive")


if __name__ == "__main__":
    main()
