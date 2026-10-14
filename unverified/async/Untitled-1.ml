
(m >>= f) >>= g
===
m >>= (fun x -> f x >>= g)


type 'a state = Resolved 'a | Pending (world -> 'a state * world);
type 'a future = Future ('a state ref)

fun return value = Future (Ref (Resolved value))

fun bind m f =

If m is Resolved v:
(m >>= f) >>= g
==>

States:
1. m is Pending
2. m is Resolved v
  a. v is cached
  b. v is not cached

Fields of m:
- value of poll m w
- effect of poll m w until it is Resolved

