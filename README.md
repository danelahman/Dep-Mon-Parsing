## Monadic parsing in the dependently typed setting

This is a simple example of monadic parsing discussed in Appendix A of my PhD thesis [1].

This example demonstrates how the parsing of typed terms is inherently dependently typed, namely, when parsing function applications, the sub-parser for argument(s) is naturally dependent on the outcome of the sub-parser for the function. The monad used in this example is the split fibred variant of the standard parser monad, itself the tensor product of the global state and the lists-based nondeterminism monads.

[1] D. Ahman. Fibred Computational Effects. PhD thesis, University of Edinburgh, 2017. ([pdf](https://danelahman.github.io/papers/phd-thesis.pdf))
