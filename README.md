# ATS Theorem proving cheatsheet

## Sorts
The statics of ATS are a simply-typed language, and the types in the language are called **sorts**. 

Commonly used built-in sorts include:

+ *bool* - static for boolean values (predictive)
+ *int* - static for integer values (predictive)
+ *type* - static for representing boxed dynamic types (impredictive)
+ *t@ype* - static for representing unboxed dynamic types (impredictive)

Commonly used static functions include:

+ `~` - integer negation - `(int) -> int`
+ `+` - addition - `(int,int) -> int`
+ `-` - subtraction - `(int,int) -> int`
+ `*` - multiplication - `(int,int) -> int`
+ `/` - division - `(int,int) -> int`
+ `>` - greater than - `(int,int) -> bool`
+ `>=` - greater than or equal - `(int,int) -> bool`
+ `<` - less than - `(int,int) -> bool`
+ `<=` - less than or equal - `(int,int) -> bool`
+ `==` - equal - `(int,int) -> bool`
+ `<>` - not equal - `(int,int) -> bool`
+ `~` - boolean negation - `(int) -> int`
+ `||` - disjunction - `(bool, bool) -> bool`
+ `&&` - conjuction - `(bool, bool) -> bool`

User-defined sorts can be made using the sortdef keyword. For example, some builtin sortdefs are:
```
sortdef nat = {a: int | a >= 0} // for natural numbers
sortdef pos = {a: int | a > 0}  // for positive numbers
sortdef neg = {a: int | a < 0}  // for negative numbers
sortdef two = {a: int | 0 <= a; a <= 1} // for 0 or 1
sortdef three = {a: int | 0 <= a; a <= 2} // for 0, 1 or 2
```

Note that the definitions for `two` and `three` could also be written as:

```
sortdef two = {a: int | a == 0 || a == 1} // for 0 or 1
sortdef three = {a: int | 0 <= a && a <= 2} // for 0, 1 or 2
```
or
```
sortdef two = {a: nat | a <= 1} // for 0 or 1
sortdef three = {a: nat | a <= 2} // for 0, 1 or 2
```

### Existential Quantifiction
One way of using sorts is to define types with existential qualification. Some definitions in ATS that use existential qualification are:
```
typedef Int = [a:int] int (a) // for unspecified integer
typedef Nat = [a:nat] int (a) // for natural numbers
```
Here `Int` and `Nat` are *existentially quantified types* which are quantified over the sorts `int` and `nat`.

For functions, the same can be done. For instance, the following is a type for a function that returns the successor of its integer argument.
```
{i:int} int(i) -> int(i+1)
```
Here `{i:int}` means universal quantification over a static variable i of the sort `int` and the scope of this quantification is the function type following.

# Dependent Datatypes
The syntax for declaring dependent datatypes is similar to the regular datatype declaration syntax:
```
datatype list(t@ype+, int) =
  | {a:t@ype} list_nil (a, 0) // of ()
  | {a:t@ype} {n:nat} list_cons(a, n+1) of (a, list(a, n))
```
`list` is now a type constructor of the sort `(t@ype, int) -> type`.

Note: `t@ype+` is used for to make `list` covariant in its first parameter (i.e. `list(T1, i)` is a subtype of `list(T2, i)` if `T1` is a subtype of `T2`). `t@ype-` could be used to make it contravariant instead, and this extends to `type+` and `type-`.

The dataconstructors `list_nil` and `list_cons` have the following types:
```
list_nil : {a:t@ype} () -> list(a, 0)
list_cons : {a:t@ype} {n:nat} (a, list(a, n)) -> list(a, n+1)
```

Note that the following datatype declaration for `list` is equivalent:
```
datatype list (a:t@ype+, int) =
  | list_nil (a, 0) of ()
  | {n:nat} list_cons(a, n+1) of (a, list(a, n))
```

# Termination Checking
Termination checking in ATS uses termination metrics. A termination metric is just a tuple of natural numbers that are ordered lexicographically that decreases. For example a recursive implementation of `fact` that can be verified to terminate is:
```
fun fact {n:nat} .<n>.
  (x: int n): int = if x > 0 then x * fact(x-1) else 1
```
Note that the metric attached to the recursive call `fact(x-1)` is `n-1` which is strictly less than the initial metric.

An example of a more complicated instance is Ackermann's function:
```
fun acker {m,n: nat} .<m,n>.
  (x : int m, y : int n): Nat =
    if x > 0 then
      if y > 0 then acker (x-1, acker(x, y-1)) else acker(x-1, 1)
    else y + 1
```

For mutually recursive functions:
```
fun isevn {n:nat} .<2*n>.
  (n: int n): bool = if n = 0 then true else isodd(n-1)
and isodd {n:nat} .<2*n+1>.
  (n : int n): bool = not (isevn n)
```
Note the tuple lengths for the mutually recursive funtions must be the same.

# Dataprops
In the ATS statics language, the built-in sort *prop* is for static terms that represent proofs. For instance, a prop construct `FIB` can be defined:
```
dataprop FIB (int, int) =
  | FIB0 (0, 0) // of ()
  | FIB1 (1, 1) // of ()
  | {n:nat} {r0, r1: nat} FIB2 (n+2, r0+r1) of (FIB(n, r0), FIB(n+1, r1))
```
The sort of `FIB` is `(int, int) -> prop`. The proof value of the prop `FIB(n, r)` can be constructed if and only if `r` is the `n`th fibonnaci number.

# Proof Functions
Consider this dataprop:
```
dataprop MUL (int, int, int) =
  | {n:int} MULbas (0, n, 0) of ()
  | {m:nat} {n:int} {p:int}
    MULind (m+1, n, p+n) of MUL (m, n, p)
  | {m:pos} {n:int} {p:int}
    MULneg (~m, n, ~p) of MUL (m, n, p)
```
and this interface for a proof function:
```
prfun mut_istot {m,n:int} (): [p:int] MUL (m, n, p)
```
`mut_istot` has the following prop that states that integer multiplication is a total function:
```
{m,n:int} () -<prf> [p:int] MUL (m, n, p)
```
`mut_istot` can be implemented as:
```
implement mul_istot {m,n} () = let
  prfun istot
    {m:nat;n:int} .<m>. (): [p:int] MUL (m, n, p) =
    sif m > 0 then MULind (istot {m-1,n} ()) else MULbas ()
in
  sif m >= 0 then istot {m,n} () else MULneg (istot {~m,n} ())
end
```
Another example is `mul_isfun` which encodes that multiplication is a function:
```
prfn mul_isfun {m,n:int} {p1,p2:int}
  (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)) : [p1==p2] void = let

  prfun isfun {m:nat;n:int} {p1,p2:int} .<m>.
    (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)) : [p1==p2] void =
    case+ pf1 of
    | MULind (pf1prev) => let
        prval MULind (pf2prev) = pf2
      in
        isfun (pf1prev, pf2prev)
      end
    | MULbas () => let
        prval MULbas () = pf2
      in
        ()
      end

in
  case+ pf1 of
  | MULneg (pf1nat) => let
      prval MULneg (pf2nat) = pf2 in isfun (pf1nat, pf2nat)
    end
  | _ =>> isfun (pf1, pf2)
end
```
Note: `prfn` is used because the function is not recursive.
# Datasort
Datasorts in the statics are analogous to datatypes in ATS dynamics. For example, to represent a binary tree in the statics:
```
datasort tree = E of () | B of (tree, tree)
```

Dataprops can then be used to capture the notion of size and height of trees:
```
dataprop SZ (tree, int) = 
  | SZE(E(), 0) // of ()
  | {tl, tr:tree} {sl, sr: nat}
    SZB(B(tl, tr), 1+sl+sr) of (SZ(tl, sl), SZ(tr, sr))

dataprop HT (tree, int) =
  | HTE(E(), 0) of ()
  | {tl, tr:tree} {hl, hr:nat}
    HTB(B(tl, tr), 1+max(hl, hr)) of (HT(tl, hl), HT(tr, hr))
```

## Example: Proof functions for tree height
Take the following dataprop encoding the power function:
```
dataprop POW2 (int, int) =
  | POW2bas(0, 1)
  | {n:nat} {p:int} POW2ind(n+1, p+p) of POW2(n, p)
```

The following elementery properties on the power function can be established:
```
prfun pow2_istot
  {h:nat} .<h>. (): [p:int] POW2 (h, p) =
  sif h > 0 then POW2ind (pow2_istot {h-1} ()) else POW2bas ()
//
prfun pow2_pos
  {h:nat} {p:int} .<h>.
  (pf: POW2 (h, p)): [p > 0] void =
  case+ pf of
  | POW2ind (pf1) => pow2_pos (pf1) | POW2bas () => ()
//
prfun pow2_inc
  {h1,h2:nat | h1 <= h2} {p1,p2:int} .<h2>.
  (pf1: POW2 (h1, p1), pf2: POW2 (h2, p2)): [p1 <= p2] void =
  case+ pf1 of
  | POW2ind (pf11) => let
      prval POW2ind (pf21) = pf2 in pow2_inc (pf11, pf21)
    end
  | POW2bas () => pow2_pos (pf2)
```
Here `pow2_istot` shows the `POW2` relation is total; `pow2_pos` proves the power of each natural number is positive; `pow2_inc` establishes that the power function is increasing.

Now, the proof function `lemma_tree_size_height`, for the `tree` datasort defined earlier, can have the signature:
```
extern
prfun lemma_tree_size_height
  {t:tree} {s,h:nat} {p:int}
  (pf1: SZ (t, s), pf2: HT (t, h), pf3: POW2 (h, p))
  : [s < p] void // end of [prfun]
```
And can be defined as:
```
implement
lemma_tree_size_height(pf1, pf2, pf3) = 
  scase t of
  | B (tl, tr) => let
      prval SZB (pf1l, pf1r) = pf1
      prval HTB {tl,tr} {hl,hr} (pf2l, pf2r) = pf2
      prval POW2ind (pf31) = pf3
      prval pf3l = pow2_istot {hl} ()
      prval pf3r = pow2_istot {hr} ()
      prval () = lemma (pf1l, pf2l, pf3l)
      prval () = lemma (pf1r, pf2r, pf3r)
      prval () = pow2_inc (pf3l, pf31)
      prval () = pow2_inc (pf3r, pf31)
    in end
  | E () => let
      prval SZE () = pf1
      prval HTE () = pf2
      prval POW2bas () = pf3
    in end
```
The termination metric for `lemma` corresponds to a proof based on structural induction. The keyword `scase` is used for static terms as `case` is for dynamic terms. Likewise, `sif` is used for static terms as `if` is used for dynamic terms.
# Sequentiality of Pattern Matching
Consider the function:
```
fun{a1,a2:t@ype}{b:t@ype}
list_zipwith {n:nat}
  (xs1: list (a1, n), xs2: list (a2, n), f: (a1, a2) -<cloref1> b)
  : list (b, n) =
  case+ (xs1, xs2) of
  | (list_cons (x1, xs1), list_cons (x2, xs2)) =>
      list_cons (f (x1, x2), list_zipwith (xs1, xs2, f))
  | (_, _) => list_nil ()
```
This does not typecheck. To make it typecheck, the second clause must be modified to:
```
  | (_, _) =>> list_nil()
```
With `=>>` the typechecker will assume that the clause must be typechecked under the sequentiality of the pattern matching, which is more expensive. Because the previous case handles the case where `(xs1, xs2)` are not empty, and because they both must have the same length, the type checker can infer that the last clause must only match `(list_nil(), list_nil())`.

Note there also exists `=/=>` which is a keyword that indicates to the typechecker of ATS that the involved clause of pattern matching is unreachable. On the right hand side of the clause the programmer must establish the falsehood.
# Circumventing Nonlinear Constraints
Consider this list concat function:
```
fun{a:t@ype} list_concat {m,n:nat}
  (xss: list (list (a, n), m)): list (a, m * n) =
  case+ xss of
  | list_cons (xs, xss) => list_append<a> (xs, list_concat xss)
  | list_nil () => list_nil ()
```
This function doesn't type check because ATS cannot solve a nonlinear constraint involving multiplication of static variables. This implementation fixes the issue:
```
fun{a:t@ype} list_concat {m,n:nat}
  (xss: list (list (a, n), m)) : [p:nat] (MUL (m, n, p) | list (a, p)) =
  case+ xss of
  | list_cons (xs, xss) => let
      val (pf | res) = list_concat (xss)
    in
      (MULind pf | list_append<a> (xs, res))
    end
  | list_nil () => (MULbas () | list_nil ())
```
Here `list_concat` returns a pair `(pf|res)` such that pf is a proof of the prop-type `MUL(m,n,p)` for some natural number p and the symbol `|` is used to separate proof from values. Here `pf` acts as a witness to the equality `p=m*n`.
# Stamping
Consider this abstract type constructor `E`:
```
sortdef elt = int // [elt] is just an alias for [int]
abst@ype E (a:t@ype, x:elt) = a // [x] is an imaginary stamp
```
The stamp `x` is imaginary and is solely used for the purpose of specification.
# Axioms
Consider this abstract prop-type MUL and a function template mul_elt_elt
```
absprop MUL (elt, elt, elt) // abstract mul relation

fun{a:t@ype}
mul_elt_elt {x,y:elt}
  (x: E (a, x), y: E (a, y)): [xy:elt] (MUL (x, y, xy) | E (a, xy))
```
The following can be used to take multiplication being associative as an axion:
```
praxi mul_assoc
  {x,y,z:elt} {xy,yz:elt} {xy_z,x_yz:elt} (
  pf1: MUL (x, y, xy), pf2: MUL (xy, z, xy_z)
, pf3: MUL (y, z, yz), pf4: MUL (x, yz, x_yz)
) : [xy_z==x_yz] void
```
Because it is specified with `praxi`, it does not need to be implemented.

