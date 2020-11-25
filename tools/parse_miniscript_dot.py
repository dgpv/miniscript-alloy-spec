#!/usr/bin/env python

import re
import sys
import pygraphviz as pgv

from typing import Set, Dict, Iterable, Tuple, Callable, Union, List

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


def to_miniscript(node: Node, next_key_name: Callable[[], str]) -> str:

    name = node.name

    if name.endswith('Wrap'):
        sep = '' if node.args[0].name.endswith('Wrap') else ':'
        return (f'{name[:1].lower()}{sep}'
                f'{to_miniscript(node.args[0], next_key_name)}')

    if name in ('After', 'Older'):
        if 'tl_height' in node.attrs['timelocks']:
            arg = 5*(10**8)+1
        else:
            assert 'tl_time' in node.attrs['timelocks']
            arg = 1

        return f'{name.lower()}({arg})'

    if name in ('Sha256', 'Hash256', 'Ripemd160', 'Hash160'):
        return f'{name.lower()}(H)'

    if name in ('Pk', 'PkH'):
        return f'{name.lower()}({next_key_name()})'

    if name == 'Zero':
        return '0'

    if name == 'One':
        return '1'

    if name == 'Multi':
        assert isinstance(node.attrs['num_args'], str)
        assert isinstance(node.attrs['required'], str)
        num_args = int(node.attrs['num_args'])
        required = int(node.attrs['required'])
        return (f'{name.lower()}({required},'
                f'{",".join(next_key_name() for _ in range(num_args))})')

    next_args = [to_miniscript(arg, next_key_name) for arg in node.args]

    if name == 'Thresh':
        assert isinstance(node.attrs['num_args'], str)
        assert isinstance(node.attrs['required'], str)
        num_args = int(node.attrs['num_args'])
        assert num_args == len(next_args)
        required = int(node.attrs['required'])
        return (f'{name.lower()}({required},{",".join(next_args)})')

    return (f'{name.lower()}({",".join(next_args)})')


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
    ms_str = to_miniscript(root, next_key_name)

    basic_type = ''
    tset = root.attrs['type']
    for t in tset:
        if t.isupper():
            assert not basic_type
            basic_type = t

    nonmal = 'yes' if 'this/MalleableSat' not in root.sets else 'no'

    # Not sure which is correct. C++ miniscript just checks for 's' flag,
    # but 's' flag can be there without has_sig.
    # hassig = 'yes' if 'this/HasSig' in root.sets else 'no'
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
