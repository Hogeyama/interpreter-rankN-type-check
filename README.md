# interpreter-rankN-type-check
OCaml-like interpreter written in Haskell with an arbitary rank type checker.
The type checker is a re-implimentaion of Jones, Simon Peyton, et al. "Practical type inference for arbitrary-rank types." Journal of functional programming 17.01 (2007): 1-82.

## Example

```
# let f : (forall a. a->int) -> int = fun g -> g true + g (g 1);;
val f : (forall a. a -> int) -> int = <fun>
# let g x = 2;;
val g : forall a. a -> int = <fun>
# f g;;
- : int = 4
# let hoge xs = match xs with
                | [] -> 0
                | y::_ -> 1;;
val hoge : forall a. a list -> int = <fun>
# let f (hoge : forall a. a list -> int) = hoge [] + hoge (1::[]);;
val f : (forall a. a list -> int) -> int = <fun>
# f hoge;;
- : int = 1
```
