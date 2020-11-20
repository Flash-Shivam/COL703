# File Structure
- `formula.ml`: Basic structure of a formula. Do not change this file.
- `bdd.mli`: Interface of bdd module. Do not change this file.
- `bdd.ml`: Implementation of bdd module. You need to implement the functions in bdd interface. You can define additional functions if needed
- `A2.ml`: The functions in this file uses the BDD module to solve the n_queen or knight's tour problem. You need to implement only one of these and leave the other one as it is. You can define additional functions if needed

# Compilation and Execution
You can compile the whole project as 
```
ocamlc formula.ml bdd.mli bdd.ml A2.ml
```
To run the package simply execute `a.out` file generated. If you wish to compile part of the assignment, you can change the names in the command accordingly.

# Submission Instrution 
Submit one .zip file to the programming assignment named 'A2: BDD' on gradescope.com. The name of the file should be `<yourEntryNumber>.zip`. On unzipping the file, it should produce files `bdd.ml`, `bdd.mli` and `A2.ml`. 

