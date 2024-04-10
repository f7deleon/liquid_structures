### Liquid Structures

This repository hosts a collection of data structures writed in LiquidHaskell. Included are implementations of three structures: ABB, AVL, and BraunTrees.

#### How to Use

To utilize this repository, ensure your environment meets the requirements specified by LiquidHaskell. The recommended setup includes the installation of z3 alongside ghc-8.10.7.

To execute the code, follow these steps:

1. Open a terminal and navigate to the main folder of the repository.
2. Run one of the following commands:

```bash
stack ghci
```
or 
```bash
stack build
```

#### File Structure

The implementations of the structures are organized within the `src` folder. Here's a breakdown:

- **ABB**:
  - External trees implementation: `ABBTreesExt.hs`
  - Internal trees implementation: `ABBTressInt.hs`
  
- **AVL Trees**:
  - Implementation: `AVLTrees.hs`
  
- **BraunTrees**:
  - Implementation: `BraunTress.hs`

- **Improved List**:
  - List with modified signatures and liquid types: `ImprovedList.hs`

- **Auxiliary Types**:
  - `IRow.hs` and `IArray.hs` contain auxiliary types utilized to prove the length equality of a BraunTree and a list.

- **Proofs**:
  - The file `ArrayXS.hs` contains various proofs conducted over the BraunTrees structure.

Feel free to explore and experiment with the implementations to gain insights into their functionality and usage.