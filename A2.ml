open Formula;;
open Bdd;;

(* 	The type of n_queen is int -> string list, where int is the 
	size of board. The solution is represented as list of strings, 
	where each string denotes the position of a queen in the solution. 
	The position is a string 'c' (lower case c without quotes) 
	appended with two single digit integers i and j, where i and j 
	are row and column numbers respectively, starting from 0. 
	For example, the string for cell in row 0 and column 4 should be c04. 
*)
let n_queen board_size = raise BDD.Not_implemented ;;

(*	The type of  knight is int -> int -> int -> string list, where
	first int is board size, second and third ints represent the
	row and column number (starting from 0) respectively of 
	initial position of the knight on the board
	The output to this function should be a sequence of strings.
	The first element in the sequence should be cell name 
	corresponding to the initial position of the knight. 
	Each subsequent string in the sequence should represent the 
	next cell visited by the knight. 
*)
let knight board_size init_row init_col = raise BDD.Not_implemented ;;	

