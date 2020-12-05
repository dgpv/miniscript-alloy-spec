#!/usr/bin/env python3

# Copyright 2020 Dmitry Petukhov https://github.com/dgpv
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

import re
import sys
import pygraphviz as pgv

from typing import (
    Set, Dict, Iterable, Tuple, Callable, Union, List, Any, Generator
)

AttrType = Union[Set[str], List[str], str]


class Node:
    def __init__(self, name: str, sets: Set[str], attrs: Dict[str, AttrType],
                 args: Iterable['Node'] = ()) -> None:
        self.name = name
        self.sets = sets
        self.attrs = attrs
        self.args = list(args)

    def __repr__(self) -> str:
        return (f'{self.__class__.__name__}({repr(self.name)}, {self.sets}, '
                f'{self.attrs}, args={self.args})')


def flatten(lst: Iterable[Any]) -> Generator[Any, None, None]:
    for item in lst:
        if isinstance(item, list):
            for subitem in flatten(item):
                yield subitem
        else:
            yield item


def flatten_op_list(lst: List[Any]) -> Generator[Any, None, None]:
    for item in flatten(lst):
        if isinstance(item, str) and not item.isdigit() \
                and not item.startswith('<'):
            yield f'OP_{item}'
        else:
            yield f'{item}'


def from_label(gvnode: pgv.Node) -> Tuple[str, Set[str], Dict[str, AttrType]]:
    node_name, sets_str, *attr_strings = gvnode.attr['label'].split("\\n")

    attrs: Dict[str, AttrType] = {}

    node_sets = set()
    for sname in sets_str.lstrip('(').rstrip(')').split(', '):
        node_sets.add(sname)

    for astring in attr_strings:
        aname, avalue = astring.split(': ', maxsplit=1)

        if aname == 'type':
            attrs[aname] = set(avalue.split(', '))
        elif aname in 'wit':
            wits = avalue.split(', ')
            wit_array = ['' for _ in wits]
            for wstr in wits:
                idx, wval = wstr.split('->')
                wit_array[int(idx)] = wval
            attrs[aname] = wit_array
        elif aname in 'timelocks':
            attrs[aname] = set(avalue.split(', '))
        else:
            attrs[aname] = avalue

    return node_name, node_sets, attrs


def process_nodes(g: pgv.AGraph) -> Node:
    nodes = {str(gvnode): from_label(gvnode) for gvnode in g.nodes()}
    root_node = None
    for gvn, ndata in nodes.items():
        if 'this/RootNode' in ndata[1]:
            root_node = gvn
            break
    else:
        print("Error: cannot find root node\n")
        sys.exit(-1)

    def walk(rn: pgv.Node) -> Node:
        args_dict = {}
        for n in g.successors(rn):
            e = pgv.Edge(g, rn, n)
            m = re.match('^args\\s+\\[(\\d+)\\]$', e.attr['label'])
            assert m
            arg_idx = int(m.group(1))
            assert arg_idx not in args_dict
            args_dict[arg_idx] = walk(n)

        args = [args_dict[idx] for idx in range(len(args_dict))]

        return Node(*nodes[rn], args=args)

    return walk(root_node)


# mypy does not support recursive types yet, have to use List[Any]
ScriptTree = List[Union[str, int, List[Any]]]


def add_verify(X: ScriptTree) -> None:
    last_op = X[-1]

    if not isinstance(last_op, str):
        if isinstance(last_op, int):
            X.append('VERIFY')
        else:
            add_verify(last_op)
        return

    if last_op in ('CHECKLOCKTIMEVERIFY', 'CHECKSEQUENCEVERIFY'):
        X.append('VERIFY')  # pointles, but allowed
        return

    if last_op.endswith('VERIFY'):
        return

    if last_op in ('EQUAL', 'NUMEQUAL', 'CHECKSIG', 'CHECKMULTISIG'):
        X[-1] = last_op + 'VERIFY'
        return

    X.append('VERIFY')


def wrapper_to_script(node: Node, X: ScriptTree) -> ScriptTree:
    name = node.name

    assert name.endswith('Wrap')

    if name.startswith('A'):
        return ['TOALTSTACK', X, 'FROMALTSTACK']

    if name.startswith('S'):
        return ['SWAP', X]

    if name.startswith('C'):
        return [X, 'CHECKSIG']

    if name.startswith('D'):
        return ['DUP', 'IF', X, 'ENDIF']

    if name.startswith('V'):
        add_verify(X)
        return X

    if name.startswith('J'):
        return ['SIZE', '0NOTEQUAL', 'IF', X, 'ENDIF']

    if name.startswith('N'):
        return [X, '0NOTEQUAL']

    assert False, f'unknown wrapper {name}'


def maybe_wit(node: Node, knames: Iterable[str] = ()) -> List[str]:
    if 'this/IgnoredNode' in node.sets or \
            'this/TransitivelyIgnoredNode' in node.sets:
        return []

    if 'wit' not in node.attrs:
        return []

    name_iter = iter(knames)
    result = []
    for wit in node.attrs['wit']:
        if wit == 'ValidSig':
            result.append(f'sig:{next(name_iter)}')
        elif wit in ('DummyWitness', 'EmptySig'):
            result.append('""')
        elif wit == 'CorrectPreimage':
            result.append(f'{node.name.lower()}:good')
        elif wit == 'WrongPreimage':
            result.append(f'{node.name.upper()}:bad')
        elif wit == 'PubKey':
            result.append(f'pub:{next(name_iter)}')
        elif wit == 'WitOne':
            result.append(f'1')
        elif wit == 'WitZero':
            result.append(f'0')
        else:
            assert False, f"unexpected witness {wit}"

    return result


def to_miniscript(node: Node, next_key_name: Callable[[], str]
                  ) -> Tuple[str, ScriptTree, List[str]]:

    name = node.name

    if name.endswith('Wrap'):
        sep = '' if node.args[0].name.endswith('Wrap') else ':'
        ms, scr, wit = to_miniscript(node.args[0], next_key_name)
        return ((f'{name[:1].lower()}{sep}{ms}'),
                wrapper_to_script(node, scr),
                maybe_wit(node) + wit)

    if name in ('After', 'Older'):
        if 'tl_height' in node.attrs['timelocks']:
            arg_ms = '500000001'
            arg_scr = '<0165cd1d>'
        else:
            assert 'tl_time' in node.attrs['timelocks']
            arg_ms = arg_scr = '1'

        ltype = 'SEQUENCE' if name == 'Older' else 'LOCKTIME'

        return (f'{name.lower()}({arg_ms})',
                [arg_scr, f'CHECK{ltype}VERIFY'],
                [])

    if name in ('Sha256', 'Hash256', 'Ripemd160', 'Hash160'):
        return (f'{name.lower()}(H)',
                ['SIZE', '<20>', 'EQUALVERIFY', name.upper(), '<H>', 'EQUAL'],
                maybe_wit(node))

    if name == 'Pk_k':
        kname = next_key_name()
        return (f'{name.lower()}({kname})',
                [f'<{kname}>'],
                maybe_wit(node, [kname]))

    if name == 'Pk_h':
        kname = next_key_name()
        return (f'{name.lower()}({kname})',
                ['DUP', 'HASH160', f'<HASH160({kname})>', 'EQUALVERIFY'],
                maybe_wit(node, [kname, kname]))

    if name == 'Zero':
        return '0', [0], []

    if name == 'One':
        return '1', [1], []

    ops: ScriptTree

    if name == 'Multi':
        assert isinstance(node.attrs['num_args'], str)
        assert isinstance(node.attrs['required'], str)
        num_args = int(node.attrs['num_args'])
        required = int(node.attrs['required'])
        knames = [next_key_name() for _ in range(num_args)]
        ops = [required]
        ops.extend([f'<{kn}>' for kn in knames])
        ops.append(num_args)
        ops.append('CHECKMULTISIG')
        return (f'{name.lower()}({required},{",".join(knames)})', ops,
                maybe_wit(node, knames))

    next_args = [to_miniscript(arg, next_key_name) for arg in node.args]

    next_ms = [arg[0] for arg in next_args]
    next_ops = [arg[1] for arg in next_args]
    next_wit = list(flatten(arg[2] for arg in next_args))

    if name == 'Thresh':
        assert isinstance(node.attrs['num_args'], str)
        assert isinstance(node.attrs['required'], str)
        num_args = int(node.attrs['num_args'])
        assert num_args == len(next_args)
        required = int(node.attrs['required'])

        ops = [next_ops[0]]
        for op in next_ops[1:]:
            ops.append(op)
            ops.append('ADD')

        ops.append(required)
        ops.append('EQUAL')

        return (f'{name.lower()}({required},{",".join(next_ms)})', ops,
                next_wit)

    if name == 'Andor':
        X, Y, Z = next_ops
        ops = [X, 'NOTIF', Z, 'ELSE', Y, 'ENDIF']
    elif name == 'And_v':
        X, Y = next_ops
        ops = [X, Y]
    elif name == 'And_b':
        X, Y = next_ops
        ops = [X, Y, 'BOOLAND']
    elif name == 'Or_b':
        X, Z = next_ops
        ops = [X, Z, 'BOOLOR']
    elif name == 'Or_c':
        X, Z = next_ops
        ops = [X, 'NOTIF', Z, 'ENDIF']
    elif name == 'Or_d':
        X, Z = next_ops
        ops = [X, 'IFDUP', 'NOTIF', Z, 'ENDIF']
    elif name == 'Or_i':
        X, Z = next_ops
        ops = ['IF', X, 'ELSE', Z, 'ENDIF']
    else:
        assert False, f'unhandled miniscript fragment {name}'

    return (f'{name.lower()}({",".join(arg[0] for arg in next_args)})',
            ops, maybe_wit(node) + next_wit)


key_idx = 0


def next_key_name() -> str:
    global key_idx

    key_idx += 1
    if key_idx == 8:
        key_idx += 1  # skip 'H' to avoid confusion with hash preimage

    assert key_idx < 26

    return chr(ord('A')+key_idx-1)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('please provide .dot file\n')
        sys.exit(-1)

    root = process_nodes(pgv.AGraph(sys.argv[1]))
    ms_str, ms_ops, wit = to_miniscript(root, next_key_name)

    basic_type = ''
    tset = root.attrs['type']
    for t in tset:
        if t.isupper():
            assert not basic_type
            basic_type = t

    if 'this/NonMalleableHolds' in root.sets:
        nonmal = 'yes'
    else:
        nonmal = 'no'

    hassig = 'yes' if 's' in tset else 'no'

    if 'f' in tset:
        dissat = 'no'
    elif 'e' in tset:
        dissat = 'unique'
    elif 'd' in tset:
        dissat = 'yes'
    else:
        dissat = 'unknown'

    if 'z' in tset:
        inp = '0'
    elif 'o' in tset:
        inp = '1n' if 'n' in tset else '1'
    elif 'n' in tset:
        inp = 'n'
    else:
        inp = '-'

    outp = '1' if 'u' in tset else 'nonzero'

    print(f'type={basic_type} safe={hassig} nonmal={nonmal} '
          f'dissat={dissat} input={inp} output={outp} miniscript={ms_str}')
    print('script:', ' '.join(flatten_op_list(ms_ops)))
    print('witness:', ' '.join(wit))
