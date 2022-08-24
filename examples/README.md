# Sudoku PLONK circuit

Checking a sudoku means that each line, column and small square is a permutation of `[1,...,9]`.
Hence, the circuit we want to build is basically 27 permutation checks.

## Permutation
We use Lemma A.3 of [this paper](https://eprint.iacr.org/archive/2019/953/1656500364.pdf) (warning: this lemma has been removed in the [latest version](https://eprint.iacr.org/archive/2019/953/20220818:162033)), with `a = [1,...,9]` and `b` the lines, columns and small squares.
This lemma requires a random field element `gamma`. We generate it using a Fiat-Shamir transform, meaning that we need a hash circuit. We consider here the Poseidon hash function implementation available in ZK-Garage.
We define a `permutation_gadget` and a `fiat_shamir_gadget` functions in order to build these two circuits. As the permutation checks a polynomial equation (when `b_i` are seen as the variables), we also need circuits for field additions and multiplications (already available in Vamp-IR if I understood correctly the presentation of the pythagorean circuit).
A permutation can be seen as one Poseidon hash and few additions and multiplications. The hash part is the most expensive but we will see that we can use only one hash for the 27 permutations.

## Sudoku circuit
Instead of generating a new `gamma` for each permutation, we can generate `gamma` once as a Fiat-Shamir transform of the entire sudoku.
We store the sudoku entries as bytes but each entry is actually 4-bit long. We can represent the sudoku with 81 * 4 = 324 bits.
Poseidon hash takes as input fields elements. In our context, field elements are 256-bit long and so we need two field elements: `1<324/256<2`.
Finally, the Sudoku circuit is split as:
* A Poseidon hash circuit with two inputs,
* 27 permutation circuits.

## Size and cost
### Circuit
Our current circuit is composed of 2048 gates.
### Proof size
PLONK proofs are fully succint. If I remember correctly, it includes 16 (base) field elements, so approximately 6kb.
### Timings
A quick benchmark can be obtained with:
```
cargo run --example sudoku --release
```
I obtained in my machine (`Intel(R) Core(TM) i5-10300H CPU @ 2.50GHz`)
```
setup: 			90ms
key generation: 	385ms
proof: 			382ms
verification: 		7ms
```
