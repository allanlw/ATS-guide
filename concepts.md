# ATS - Turtles All The Way Down

- *sort* - A sort is the most basic concept in ATS. The statics of ATS 
is a simply-typed language (thus, there is no recursion in the static of
ATS), and the types in this language are called 
*sorts*. Some example sorts include `bool`, `int`, `type`, `t@ype`, and 
`prop`, which are used to represent static terms of boolean values, 
integer values, boxed types, unboxed types and proofs, respectively. 
Note that sorts can also have function types such as `(int, int) -> 
int`.

## Examples of sorts
- *datasort* - A user-defined sort that is associated with a number of 
data sort constructors, which store static values. Cannot be 
paramterized with static values. Contrast with *datatype* and 
*dataprop*.

- *type* and *t@ype* - A type is a very specific form of static values 
of the sort `type` or `t@ype`. Types are used in the ATS dynamic 
language (the main ats language, _per se_).

- *prop* - A prop is a specific form of static value that represents a 
type of a proof. They are similar to types, but are not instantiated at 
compile time.

- *view* - used for representing static terms representing memory views.

- *viewtype* and *viewt@ype* - used for representing tuples of views and 
types. Correspond to `type` and `t@ype`.

## Examples of non-type, non-prop static values
- *static value* - Static values are simply instantiations of a `sort` 
in the ATS statics language. All static values are gone after proof 
erasure, and do not result in generated code.

- *type constructor* - A type constructor is a static value that takes 
any number of arguments (potentially zero) and returns a static value of 
kind `t@ype` or `type`. For example, the type constructor `list0` is of 
sort `(t@ype) -> type`.

- *prop constructor* - This is the same as a type constructor except the 
return value is `prop`.

## Examples of types
- *datatype* - Datatypes are specific types of user-defined types that 
are associated with some number of *data constructors*, which are 
essentially (dynamic) functions can be used to construct objects of the 
datatype and that can also be pattern matched on. Contrast with 
*datasort* and *dataprop*.

## Examples of dynamic values
- *dynamic value* - Dynamic values are instantiations of a `type`. These 
are program runtime values in the classical sense.

- *(dynamic) function* - A function declared with the *fun* keyword, 
which accepts dynamic value arguments and returns a dynamic value. It 
can be parameterized on sorts.

## Examples of props
- *dataprop* - Dataprops are similar to datatypes for types and 
datasorts for sorts. They provide a mechanism for encoding relationships 
between static terms. When custom dataprops are defined, they are prop 
constructors that have a sort for a static function that returns a value 
of sort `prop`. They also have prop constructors, which are prop 
functions that take prop values and returns a prop value. Contrast with 
*datatype* and *datasort*.

## Examples of prop values
- *prop value* - A prop value is an instantiations of a `prop`. These 
represent an encoding for a relation between variables, which can also 
be thought of as a proof.

- *proof function* - A function declared with the *prfun* keyword, which 
accepts prop value arguments and returns a prop value. It can be 
parameterized on sorts (and normally is).

- *proof axiom* - A function declared with the *praxi* keyword, which 
makes it an axiom, which does not have to be, and cannot be implemented. 
It can be parameterized on sorts (and normally is).

# Polymorphism
Polymorphism is accomplished at ATS by paramaterizing over sorts.

An example of datatype polymorphism:
```
datatype list0(a:t@ype) =
  | list0_nil(a) of ()
  | list0_cons(a) of (a, list0(a))
```
Here `list` is declared as a type constructor of the sort 
`(t@ype)->type`. The types of the two dataconstructors are:
```
list0_nil : {a:t@ype} () -> list0(a)
list0_cons : {a:t@ype} (a, list(a)) -> list(a)
```

An example of function polymorphism:
```
fun swam_boxed {a,b:type} (xy: (a, b)): (b, a) = (xy.1, xy.0)
```
Here `swap_boxed` has the type:
```
swap_boxed : {a,b:type} ((a,b)) -> (b,a)
```

Note than in either example, an arbtirary sort could be used. 
Furthermore, datatype and function polymorphism is exactly the same for 
props.
