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

# Proof Functions
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

Now, the proof function `lemma_tree_size_height` can have the signature:
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
