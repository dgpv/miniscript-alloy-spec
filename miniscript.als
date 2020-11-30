// Miniscript specification (c) by Dmitry Petukhov (https://github.com/dgpv)
// Licensed under a Creative Commons Attribution-ShareAlike 4.0 International
// License <http://creativecommons.org/licenses/by-sa/4.0/>

module miniscript

open util/ternary
open util/graph[Node]

// The specification consists of four sections. First is the Nodes section,
// which presents the node specifications that references witnesses defined
// in Witnesses section and is using the definitions from the Definitions
// section. The predicates, run and check clauses for analysis of this
// specification are in the Analysis section.

/*****************/
/* Nodes section */
/*****************/

sig Zero extends Node {
} {
    type = B + z + u + d + s + e

    no args
    no wit

    correctness_holds
    non_malleability_holds

    never  [ sat ]
    always [ dsat ]

    never  [ nc_sat ]
    never  [ nc_dsat ]

    no timelocks
}

sig One extends Node {
} {
    type = B + z + u + f

    no args
    no wit

    correctness_holds
    non_malleability_holds

    always [ sat ]
    never  [ dsat ]

    never  [ nc_sat ]
    never  [ nc_dsat ]

    no timelocks
}

sig Pk extends Node {
} {
    type = K + o + n + d + u + s + e

    no args

    #wit = 1

    wit[0] in Sig

    correctness_holds
    non_malleability_holds

    xpect [ sat,  wit[0] in ValidSig ]
    xpect [ dsat, wit[0] in EmptySig ]

    never [ nc_sat ]
    never [ nc_dsat ]

    no timelocks
}

sig PkH extends Node {
} {
    type = K + n + u + d + s + e

    no args

    #wit = 2

    wit[0] in PubKey
    wit[1] in Sig

    correctness_holds
    non_malleability_holds

    xpect [ sat,  wit[1] in ValidSig ]
    xpect [ dsat, wit[1] in EmptySig ]

    never [ nc_sat ]
    never [ nc_dsat ]

    no timelocks
}

abstract sig Timelock extends Node {
} {
    type = B + z + f

    no args
    no wit

    correctness_holds
    non_malleability_holds

    always [ sat ]
    never  [ dsat ]

    never  [ nc_sat ]
    never  [ nc_dsat ]

    timelocks = tl_height or timelocks = tl_time
}

sig Older extends Timelock {}
sig After extends Timelock {}

abstract sig Hash extends Node {
} {
    type = B + o + n + u + d

    no args

    #wit = 1

    wit[0] in Preimage

    correctness_holds
    non_malleability_holds

    xpect  [ sat,  wit[0] in CorrectPreimage ]
    xpect  [ dsat, wit[0] in WrongPreimage ]

    never  [ nc_sat ]
    never  [ nc_dsat ]

    no timelocks
}

sig Sha256 extends Hash {}
sig Hash256 extends Hash {}
sig Ripemd160 extends Hash {}
sig Hash160 extends Hash {}

sig Andor extends Node {
} {
    no wit

    #args = 3

    let X = args[0], Y = args[1], Z = args[2]
    {
        type = btype[Y]
               + maybe [ z,  z[X] and z[Y] and z[Z] ]
               + maybe [ o, (z[X] and o[Y] and o[Z]) or
                            (o[X] and z[Y] and z[Z]) ]
               + maybe [ u,  u[Y] and u[Z] ]
               + maybe [ d,  d[Z] ]
               + maybe [ s,  s[Z] and (s[X] or s[Y]) ]
               + maybe [ f,  f[Z] and (s[X] or f[Y]) ]
               + maybe [ e,  e[Z] and (s[X] or f[Y]) ]

        xpect [
            correctness_holds,
            {
                B + d + u in X.@type
                btype[Y] in B + K + V
                btype[Z] = btype[Y]
            }
        ]

        xpect [ non_malleability_holds, e[X] and (s[X] or s[Y] or s[Z]) ]

        xpect [
            sat, (sat[Y] and  sat[X]) or
                 (sat[Z] and dsat[X])
        ]
        xpect [ dsat, (dsat[Z] and dsat[X]) or nc_dsat ]

        never [ nc_sat ]
        xpect [ nc_dsat, dsat[Y] and sat[X] ]

        timelocks = timelocks_combined[X + Y] + timelocks_combined[X + Z]

        args.ignored = ( dsat[X] => Y else Z )
    }
}

sig And_v extends Node {
} {
    no wit

    #args = 2

    let X = args[0], Y = args[1]
    {
        type = btype[Y]
               + maybe [ z, (z[X] and z[Y]) ]
               + maybe [ o, (z[X] and o[Y]) or
                            (z[Y] and o[X]) ]
               + maybe [ n,  n[X] or
                            (z[X] and n[Y]) ]
               + maybe [ u,  u[Y] ]
               + maybe [ s,  s[X] or  s[Y] ]
               + maybe [ f,  s[X] or  f[Y] ]

        xpect [
            correctness_holds,
            {
                btype[X] in V
                btype[Y] in B + K + V
            }
        ]

        non_malleability_holds

        xpect [ sat,  sat[Y] and sat[X] ]
        xpect [ dsat, nc_dsat ]

        never [ nc_sat ]
        xpect [ nc_dsat, dsat[Y] and sat[X] ]

        timelocks = timelocks_combined[X + Y]

        no args.ignored
    }
}

sig And_b extends Node {
} {
    no wit

    #args = 2

    let X = args[0], Y = args[1]
    {
        type = B + maybe [ z, (z[X] and z[Y]) ]
                 + maybe [ o, (z[X] and o[Y]) or
                              (z[Y] and o[X]) ]
                 + maybe [ n,  n[X] or
                              (z[X] and n[Y]) ]
                 + maybe [ d,  d[X] and d[Y] ]
                 + just  [ u ]
                 + maybe [ s,  s[X] or  s[Y] ]
                 + maybe [ f, (f[X] and f[Y]) or
                              (s[X] and f[X]) or
                              (s[Y] and f[Y]) ]
                 + maybe [ e,  e[X] and e[Y] and s[X] and s[Y] ]

        xpect [
            correctness_holds,
            {
                btype[X] in B
                btype[Y] in W
            }
        ]

        non_malleability_holds

        xpect [ sat,    sat[Y] and  sat[X] ]
        xpect [ dsat, (dsat[Y] and dsat[X]) or nc_dsat ]

        never [ nc_sat ]
        xpect [ nc_dsat, ( sat[Y] and dsat[X]) or
                         (dsat[Y] and  sat[X]) ]

        timelocks = timelocks_combined[X + Y]

        no args.ignored
    }
}

sig Or_b extends Node {
} {
    no wit

    #args = 2

    let X = args[0], Z = args[1]
    {
        type = B + maybe [ z, (z[X] and z[Z]) ]
                 + maybe [ o, (z[X] and o[Z]) or
                              (z[Z] and o[X]) ]
                 + just  [ d ]
                 + just  [ u ]
                 + maybe [ s, (s[X] and s[Z]) ]
                 + just  [ e ]

        xpect [
            correctness_holds,
            {
                B + d in X.@type
                W + d in Z.@type
            }
        ]

        xpect [ non_malleability_holds, e[X] and e[Z] and (s[X] or s[Z]) ]

        xpect [
            sat, (dsat[Z] and  sat[X]) or
                 ( sat[Z] and dsat[X]) or
                 nc_sat
        ]
        xpect [ dsat, dsat[Z] and dsat[X] ]

        xpect [ nc_sat, sat[Z] and sat[X] ]
        never [ nc_dsat ]

        timelocks = (@timelocks[X] + @timelocks[Z])

        no args.ignored
    }
}

sig Or_c extends Node {
} {
    no wit

    #args = 2

    let X = args[0], Z = args[1]
    {
        type = V + maybe [ z, z[X] and z[Z] ]
                 + maybe [ o, o[X] and z[Z] ]
                 + maybe [ s, s[X] and s[Z] ]
                 + just  [ f ]

        xpect [
            correctness_holds,
            {
                B + d + u in X.@type
                btype[Z] in V
            }
        ]

        xpect [ non_malleability_holds, e[X] and (s[X] or s[Z]) ]

        xpect [ sat, sat[X] or (sat[Z] and dsat[X]) ]
        never [ dsat ]

        never [ nc_sat ]
        never [ nc_dsat ]

        timelocks = (@timelocks[X] + @timelocks[Z])

        args.ignored = maybe [ Z, sat[X] ]
    }
}

sig Or_d extends Node {
} {
    no wit

    #args = 2

    let X = args[0], Z = args[1]
    {
        type = B + maybe [ z, z[X] and z[Z] ]
                 + maybe [ o, o[X] and z[Z] ]
                 + maybe [ d, d[Z] ]
                 + maybe [ u, u[Z] ]
                 + maybe [ s, s[X] and s[Z] ]
                 + maybe [ f, f[Z] ]
                 + maybe [ e, e[Z] ]

        xpect [
            correctness_holds,
            {
                B + d + u in X.@type
                btype[Z] in B
            }
        ]

        xpect [ non_malleability_holds, e[X] and (s[X] or s[Z]) ]

        xpect [ sat,  sat[X] or (sat[Z] and dsat[X]) ]
        xpect [ dsat, dsat[Z] and dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        timelocks = (@timelocks[X] + @timelocks[Z])

        args.ignored = maybe [ Z, sat[X] ]
    }
}

sig Or_i extends Node {
} {
    #wit = 1

    wit[0] in WitBool

    #args = 2

    let X = args[0], Z = args[1]
    {
        type = btype[X]
               + maybe [ o,  z[X] and z[Z] ]
               + maybe [ u,  u[X] and u[Z] ]
               + maybe [ d,  d[X] or  d[Z] ]
               + maybe [ s,  s[X] and s[Z] ]
               + maybe [ f,  f[X] and f[Z] ]
               + maybe [ e, (e[X] and f[Z]) or
                            (e[Z] and f[X]) ]

        xpect [
            correctness_holds,
            {
                btype[X] in B + K + V
                btype[X] = btype[Z]
            }
        ]

        xpect [ non_malleability_holds, s[X] or s[Z] ]

        xpect [ sat,  wit[0] in WitZero =>  sat[Z] else  sat[X] ]
        xpect [ dsat, wit[0] in WitZero => dsat[Z] else dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        timelocks = (@timelocks[X] + @timelocks[Z])

        args.ignored = ( wit[0] in WitZero => X else Z )
    }
}

sig Thresh extends Node {
    num_args: Int,
    required: Int
} {
    no wit

    #args = num_args
    1 < required
    required < num_args

    type = B + maybe [ z, all arg: args.elems | z[arg] ]
             + maybe [ o, one arg_o: args.elems, args_non_o: args.elems - arg_o
                          {
                               o[arg_o]
                               all arg: args_non_o | z[arg]
                          } ]
             + just  [ d ]
             + just  [ u ]
             + maybe [ s, #{ arg: args.elems | not s[arg] } <= required.minus[1] ]
             + maybe [ e, all arg: args.elems | s[arg] ]

    xpect [
        correctness_holds,
        {
            B + d + u in args.first.@type
            all arg: args.rest.elems {
                W + d + u in arg.@type
            }
        }
    ]

    xpect [
        non_malleability_holds,
        {
            all arg: args.elems | e[arg]
            #{ arg: args.elems | not s[arg] } <= required
        }
    ]

    let num_sats  = #{arg: args.elems |  sat[arg]},
        num_dsats = #{arg: args.elems | dsat[arg]}
    {
        xpect [ sat,  num_sats = required ]
        xpect [ dsat, num_dsats = num_args or nc_dsat ]

        never [ nc_sat ]
        xpect [ nc_dsat, num_sats != required and num_dsats != num_args ]
    }

    timelocks = timelocks_combined[args.elems]

    no args.ignored
}

sig Multi extends Node {
    num_args: Int,
    required: Int
} {
    num_args <= 20
    1 < required
    required < num_args

    no args

    non_malleability_holds

    #wit = required.plus[1]
    wit.last in DummyWitness
    all wt: wit.butlast.elems | wt in Sig

    type = B + n + d + u + s + e

    let all_empty = (all wt: wit.butlast.elems | wt in EmptySig),
        all_valid = (all wt: wit.butlast.elems | wt in ValidSig)
    {
        all_empty or all_valid  // Otherwise fails with ERR_SIG_NULLFAIL

        xpect [ sat,  all_valid ]
        xpect [ dsat, all_empty ]

        never [ nc_sat ]
        never [ nc_dsat ]
    }

    no timelocks
}

abstract sig Wrapper extends Node {
} {
    #args = 1

    non_malleability_holds

    timelocks = @timelocks[args[0]]
}

sig AWrap extends Wrapper {
} {
    no wit

    let X = args[0]
    {
        xpect [ correctness_holds, B in X.@type ]

        type = W + maybe [ d, d[X] ]
                 + maybe [ u, u[X] ]
                 + maybe [ s, s[X] ]
                 + maybe [ f, f[X] ]
                 + maybe [ e, e[X] ]

        xpect [ sat,   sat[X] ]
        xpect [ dsat, dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        no args.ignored
    }
}

sig SWrap extends Wrapper {
} {
    no wit

    let X = args[0]
    {
        xpect [ correctness_holds, B + o in X.@type ]

        type = W + maybe [ d, d[X] ]
                 + maybe [ u, u[X] ]
                 + maybe [ s, s[X] ]
                 + maybe [ f, f[X] ]
                 + maybe [ e, e[X] ]

        xpect [ sat,   sat[X] ]
        xpect [ dsat, dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        no args.ignored
    }
}

sig CWrap extends Wrapper {
} {
    no wit

    let X = args[0]
    {
        xpect [ correctness_holds, K in X.@type ]

        type = B + maybe [ o, o[X] ]
                 + maybe [ n, n[X] ]
                 + maybe [ d, d[X] ]
                 + just  [ u ]
                 + just  [ s ]
                 + maybe [ e, e[X] ]

        xpect [ sat,   sat[X] ]
        xpect [ dsat, dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        no args.ignored
    }
}

sig DWrap extends Wrapper {
} {
    #wit = 1

    wit[0] in WitBool

    let X = args[0]
    {
        xpect [ correctness_holds, V + z in X.@type ]

        type = B + o + n + d + u
                 + maybe [ s, s[X] ]
                 + just  [ e ]

        xpect [ sat,  wit[0] in WitOne  ] // sat[X] is irrelevant because X is V
        xpect [ dsat, wit[0] in WitZero ]

        never [ nc_sat ]
        never [ nc_dsat ]

        args.ignored = maybe [ X, wit[0] in WitZero ]
    }
}

sig VWrap extends Wrapper {
} {
    no wit

    let X = args[0]
    {
        xpect [ correctness_holds, B in X.@type ]

        type = V + maybe [ z, z[X] ]
                 + maybe [ o, o[X] ]
                 + maybe [ n, n[X] ]
                 + maybe [ s, s[X] ]
                 + just  [ f ]

        always [ sat[X] ] // VERIFY will be applied

        always [ sat ]
        never  [ dsat ]

        never  [ nc_sat ]
        never  [ nc_dsat ]

        no args.ignored
    }
}

sig JWrap extends Wrapper {
} {
    #wit = 1 or #wit = 0
    #wit = 1 => wit[0] in WitZero

    let X = args[0]
    {
        xpect [ correctness_holds, B + n in X.@type ]

        type = B + maybe [ o, o[X] ]
                 + just  [ n ]
                 + just  [ d ]
                 + maybe [ u, u[X] ]
                 + maybe [ s, s[X] ]
                 + maybe [ e, f[X] ]

        xpect [ sat,  #wit = 0 and sat[X] ]
        xpect [ dsat, #wit > 0 or nc_dsat ]

        never [ nc_sat ]
        xpect [ nc_dsat, #wit = 0 and dsat[X] ]

        args.ignored = maybe [ X, #wit > 0 ]
    }
}

sig NWrap extends Wrapper {
} {
    no wit

    let X = args[0]
    {
        xpect [ correctness_holds, B in X.@type ]

        type = B + maybe [ z, z[X] ]
                 + maybe [ o, o[X] ]
                 + maybe [ n, n[X] ]
                 + maybe [ d, d[X] ]
                 + just  [ u ]
                 + maybe [ s, s[X] ]
                 + maybe [ f, f[X] ]
                 + maybe [ e, e[X] ]

        xpect [ sat,   sat[X] ]
        xpect [ dsat, dsat[X] ]

        never [ nc_sat ]
        never [ nc_dsat ]

        no args.ignored
    }
}

/*********************/
/* Witnesses section */
/*********************/

abstract sig Witness {}

lone sig DummyWitness extends Witness {}  // CHECKMULTISIG dummy input

abstract sig WitBool extends Witness {}
lone sig WitZero extends WitBool {}
lone sig WitOne extends WitBool {}

abstract sig Sig extends Witness {}
lone sig ValidSig extends Sig {}
lone sig EmptySig extends Sig {}

lone sig PubKey extends Witness {}

abstract sig Preimage extends Witness {}
lone sig CorrectPreimage extends Preimage {}
lone sig WrongPreimage extends Preimage {}


/***********************/
/* Definitions section */
/***********************/

// Anything that is needed for the spec to function and be readable

// The node definition
abstract sig Node {
    type: set TypeDesignator,
    args: seq Node,
    wit: seq Witness,
    timelocks: set TimelockType
} {
    V in type => this not in DSat // V cannot be dissatisfied
}

one sig RootNode in Node {
} {
    B in type
    this not in IgnoredNode
}

fact {
    treeRootedAt[args.as_set, RootNode]

    // no stray witnesses
    Witness in RootNode.*(args.as_set).wit.elems

    // no duplicate args
    (sum node: RootNode.*(args.as_set) | #node.args) = #(RootNode.^(args.as_set))
}

// more readable access to BasicType
fun btype [node: Node]: BasicType { node.type & BasicType }

// to define ignored-node relation more readably
fun ignored [a: seq Node]: set Node { a.elems & IgnoredNode }

// Convenience macro to convert sequence to set
let as_set[sq] = select13[sq]

// Node types are modelled as a single enum, from which
// subsets are drawn to designate different kind of types
//
// Using one-letter identifiers for types is a bit
// risky, because we could confuse 'z' type modifier
// with 'Z' argument, but at the same time one-letter
// types make the spec more readable, and closer to the
// original specification in prose, which also uses
// one-letter identifiers. This means that we any
// one-letter identifier we use should be directly linked
// to their spec meaning (no 'n: Node', only 'node: Node')

enum TypeDesignator { B, V, K, W, z, o, n, d, u, s, f, e }

sig BasicType in TypeDesignator {}
fact { B + V + K + W = BasicType }

sig CorrectnessTypeModifier in TypeDesignator {}
fact { z + o + n + d + u = CorrectnessTypeModifier }

sig NonmalleabilityTypeModifier in TypeDesignator {}
fact { s + f + e = NonmalleabilityTypeModifier }

pred basic_types_and_modifiers_correctly_specified {
    BasicType + CorrectnessTypeModifier + NonmalleabilityTypeModifier = TypeDesignator

    no BasicType & CorrectnessTypeModifier
    no BasicType & NonmalleabilityTypeModifier
    no NonmalleabilityTypeModifier & CorrectnessTypeModifier

    all node: Node | #btype[node] = 1 // single basic type always specified
}

// convenience predicates for type modifiers
pred z [node: Node] { z in node.type }
pred o [node: Node] { o in node.type }
pred n [node: Node] { n in node.type }
pred d [node: Node] { d in node.type }
pred u [node: Node] { u in node.type }
pred s [node: Node] { s in node.type }
pred f [node: Node] { f in node.type }
pred e [node: Node] { e in node.type }

// convenience macros for readability
let maybe  [ set_exp, cond ]  = { cond => set_exp else none }
let xpect  [ bool_exp, cond ] = { cond => bool_exp else !bool_exp }
let never  [ bool_exp ]       = { not bool_exp }
let always [ bool_exp ]       = { bool_exp }
let just   [ exp ]            = { exp }

sig Sat in Node {} // satisfied nodes
sig NC_Sat in Node {} // non-canonically satisfied nodes
sig DSat in Node {} // dissatisfied nodes
sig NC_DSat in Node {} // non-canonically dissatisfied nodes

pred sat     [node: Node] { node in Sat }
pred nc_sat  [node: Node] { node in NC_Sat }
pred dsat    [node: Node] { node in DSat }
pred nc_dsat [node: Node] { node in NC_DSat }

enum TimelockType { tl_height, tl_time, tl_conflict }

// Nodes for which combination of height and time locks is forbidden
// (Thresh and And_*) must use this function to combine timelocks of
// their args. If there's a conflict, tl_conflict will be added.
fun timelocks_combined [nodes: set Node]: set TimelockType {
    let combined = timelocks[nodes] {
        combined + maybe[ tl_conflict, tl_height + tl_time in combined ]
    }
}

// Nodes that won't be executed with current witness configuration will be
// placed in IgnoredNode and their descendands will be
// placed in TransitivelyIgnoredNode

sig IgnoredNode in Node {}

sig TransitivelyIgnoredNode in Node {}
fact { TransitivelyIgnoredNode = IgnoredNode.^(args.as_set) }

// Predicates to help define correctness and non-malleability properties

sig CorrectnessHolds in Node {}
sig NonMalleableHolds in Node {}

pred correctness_holds [node: Node] { node in CorrectnessHolds }
pred non_malleability_holds [node: Node] { node in NonMalleableHolds }

pred correctness_holds_for_all_nodes { Node = CorrectnessHolds }
pred non_malleability_holds_for_all_nodes { Node = NonMalleableHolds }

/********************/
/* Analysis section */
/********************/

// Predicates for reducing the search space for solver

pred one_is_only_used_by_And_v {
    no (One & RootNode)
    no (One & (Node - And_v).args.elems)
    no (One & And_v.args[0])
}

pred zero_is_only_used_by_Andor_and_Or_i {
    no (Zero & RootNode)
    no (Zero & (Node - Andor - Or_i).args.elems)
    no (Zero & Andor.args.butlast.elems)
}

pred no_useless_one_or_zero {
    one_is_only_used_by_And_v
    zero_is_only_used_by_Andor_and_Or_i
}

pred no_useless_wrappers {
    no wrp: Wrapper | wrp.type = wrp.args[0].type
}

pred identical_fragments_disabled {
    // Only Sha256
    no Hash256
    no Ripemd160
    no Hash160
}

pred reduced_search_space {
    identical_fragments_disabled
    Thresh.num_args <= 3
    Multi.num_args <= 3
    no_useless_one_or_zero
    no_useless_wrappers
}

// run and check clauses

pred main_search_predicate {

    reduced_search_space

    correctness_holds_for_all_nodes
    non_malleability_holds_for_all_nodes

    tl_conflict not in timelocks[RootNode]

    RootNode.sat
    s[RootNode]

}

// Note that currently there are 8 possible witness instances:
// one DummyWitness, one PubKey, two of Sig, two of Preimage, WitBool.
// If more witness types are added, the max witness counts for the
// run and check clauses should be updated.

run main {
    main_search_predicate
} for 6 but 12 Node, 8 Witness, 6 Int, 4 seq

pred sat_iff_dsat {
    correctness_holds_for_all_nodes => {
        Node = Sat + DSat and no Sat & DSat // sat iff dsat
    }
}

pred sat_s_dsat_f_always_have_valid_sig {
    {
        correctness_holds_for_all_nodes
        non_malleability_holds_for_all_nodes
    }
    implies {
        all node: Sat  | s[node] => ValidSig in node.*(args.as_set).wit.elems
        all node: DSat | f[node] => ValidSig in node.*(args.as_set).wit.elems
    }
}

pred z_o_n_modifiers_correctly_specified {
    correctness_holds_for_all_nodes => {
        all node: Node - IgnoredNode - TransitivelyIgnoredNode {
            let non_ignored_descendants =
                node.*(args.as_set) - IgnoredNode - TransitivelyIgnoredNode
            {
                z[node] => #non_ignored_descendants.wit = 0
                o[node] => #non_ignored_descendants.wit = 1
                n[node] => #non_ignored_descendants.wit >= 1
            }
        }
    }
}

check well_formed {
    basic_types_and_modifiers_correctly_specified
    NC_Sat in Sat // nc_sat implies sat
    NC_DSat in DSat // nc_dsat implies dsat
    sat_iff_dsat
    sat_s_dsat_f_always_have_valid_sig
    z_o_n_modifiers_correctly_specified
} for 5 but 8 Node, 8 Witness, 6 Int, 4 seq

// An example what of what properties we can explore.
//
// Hypothesis: there might be the case where or_b non-canonical satisfaction
// can be disabled via conflicting timelock checks in its arguments.
// Timelocks also cannot be in the ignored nodes, because otherwise
// the conflict can be avoided and non-canonical satisfaction would not be
// disabled. This hipothesis seems to be false, but it could be interesting
// to look at the counterexamples when we remove some predicates
check or_b_timelock_conflict_example {

    {
        reduced_search_space

        correctness_holds_for_all_nodes

        // We are interested to explore only scripts that are satisfied
        RootNode.sat

        // Explore only instances with
        s[RootNode]
        // and still with Or_b with conflicting timelocks.
        // We can achieve this by having Anv_v as a root node that
        // has Pk in one of its branches. We will at least 12 Nodes
        // for the search to find something, but because we fix 4 of them,
        // the search space is still manageable
        //
        // Note that this is how a full tree can be specified, when for
        // example an implementation wants to check their structures against
        // the spec. The program can produce the check clauses with trees
        // specified in similar manner and then check them in Alloy
        RootNode in And_v
        RootNode.args[0] in VWrap
        RootNode.args[0].args[0] in CWrap
        RootNode.args[0].args[0].args[0] in Pk
        RootNode.args[1] in Or_b

        // It seems that enabling this condition is enough to make this check
        // pass without counterexamples, with 12 nodes
        // (and the s[RootNode] condition above enabled). So we will not enable
        // this condition for our exploration by default, as the 'ignorable'
        // condition below seems to also be enough for that
        //non_malleability_holds_for_all_nodes

        // It seems that there can be no instances where timelocks cannot
        // be ignored with certain withess configuration.
        // This means that our hypothesis is false, at least with 12 nodes
        // (and the s[RootNode] condition above enabled).
        // If you remove this condition, you'll see some counterexamples,
        // but they would still not match our hypothesis because the timelocks
        // will be ignorable
        all node: Node { can_be_ignored [node] => no node.timelocks }
    }
    implies
    {
        no node: Or_b {
            {
                tl_time in node.args[0].timelocks
                tl_height in node.args[1].timelocks
            }
            or
            {
                tl_height in node.args[1].timelocks
                tl_time in node.args[0].timelocks
            }
        }
    }
} for 5 but 12 Node, 8 Witness, 6 Int, 4 seq

pred can_be_ignored [node: Node] {
    // We explicitly list nodes and args that has the possibility of
    // being ignored. Note that because this predicate explicitly lists
    // the nodes and args, it can become incorrect if new nodes with
    // ignorable args are added. Because of this, this predicate is defined
    // in Analysis section, close to the check clause that uses it.
    let ignorable_args = ( Andor.args[1] + Andor.args[2] +
                           Or_c.args[1] +
                           Or_d.args[1] +
                           Or_i.args[0] + Or_i.args[1] +
                           DWrap.args[0] +
                           JWrap.args[0] )
    {
        node in ignorable_args + ignorable_args.^(args.as_set)
    }
}
