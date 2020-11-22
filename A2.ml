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


let new_table = Hashtbl.create 1000;;
let rec add_to_tab size = if size = 0 then Hashtbl.add new_table size "0" else let r = Hashtbl.add new_table size (string_of_int (size)) in add_to_tab (size-1);;
let do_some size = let p = Hashtbl.clear new_table in add_to_tab (size*size-1)
;;
let rec row_cond row end_r = if row = end_r then Program.Variable(Hashtbl.find new_table row) else Program.OprBinary(Program.OR,Program.Variable(Hashtbl.find new_table row),row_cond (row-1) end_r);;

let rec make_Expr_one index1 index2 size run_iter = if run_iter = 1  then (if (run_iter = index2) then Program.Constant(true) else Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (index1-1)*size + run_iter -1 ))) ) else (if (run_iter = index2 )then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_one index1 index2 size (run_iter-1))  else Program.OprBinary(Program.AND,Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (index1-1)*size + run_iter -1 ) )),make_Expr_one index1 index2 size (run_iter-1) ));;

let rec make_Expr_two index1 index2 size run_iter = if run_iter = 1  then (if (run_iter = index1) then Program.Constant(true) else Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2 -1 )) )) else (if (run_iter = index1 )then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_two index1 index2 size (run_iter-1))  else Program.OprBinary(Program.AND,Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2 -1 ) )),make_Expr_two index1 index2 size (run_iter-1) ));;

let rec make_Expr_three index1 index2 size run_iter = if run_iter = 1  then (if (run_iter = index1 || ( run_iter <=0 || run_iter > size || (run_iter+index2-index1<=0) || (run_iter+index2-index1>size) )) then Program.Constant(true) else Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2-index1+run_iter -1 )) )) else (if (run_iter = index1 ) then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_three index1 index2 size (run_iter-1))  else ( if ( run_iter <=0 || run_iter > size || (run_iter+index2-index1<=0) || (run_iter+index2-index1>size)  ) then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_three index1 index2 size (run_iter-1) ) else Program.OprBinary(Program.AND,Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2-index1+run_iter -1 ) )),make_Expr_three index1 index2 size (run_iter-1) )));;

let rec make_Expr_four index1 index2 size run_iter = if run_iter = 1  then (if (run_iter = index1 || ( run_iter <=0 || run_iter > size || (-run_iter+index2+index1<=0) || (-run_iter+index2+index1>size)  )) then Program.Constant(true) else Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2+index1-run_iter -1 )) )) else (if (run_iter = index1 ) then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_four index1 index2 size (run_iter-1))  else ( if ( run_iter <=0 || run_iter > size || (-run_iter+index2+index1<=0) || (-run_iter+index2+index1>size)  ) then Program.OprBinary(Program.AND,Program.Constant(true),make_Expr_four index1 index2 size (run_iter-1) ) else Program.OprBinary(Program.AND,Program.OprUnary(Program.NOT,Program.Variable(Hashtbl.find new_table ( (run_iter-1)*size + index2+index1-run_iter -1 ) )),make_Expr_four index1 index2 size (run_iter-1) )));;

let m_ex_1 index1 index2 size = Program.OprBinary(Program.IFTHEN,Program.Variable(Hashtbl.find new_table ((index1-1)*size+index2-1)  ),make_Expr_one index1 index2 size size);;

let m_ex_2 index1 index2 size = Program.OprBinary(Program.IFTHEN,Program.Variable(Hashtbl.find new_table ((index1-1)*size+index2-1)  ),make_Expr_two index1 index2 size size);;

let m_ex_3 index1 index2 size = Program.OprBinary(Program.IFTHEN,Program.Variable(Hashtbl.find new_table ((index1-1)*size+index2-1)  ),make_Expr_three index1 index2 size size);;

let m_ex_4 index1 index2 size = Program.OprBinary(Program.IFTHEN,Program.Variable(Hashtbl.find new_table ((index1-1)*size+index2-1)  ),make_Expr_four index1 index2 size size);;

let rec f_iter index1 index2 size l = if index2 = size then (if index1 == size then l@[(index1,index2)] else f_iter (index1+1) (1) size l@[(index1,index2)] ) else f_iter (index1) (index2+1) size l@[(index1,index2)];;

let rec f_comp_one l size g = match l with
| [] -> g
| head :: tail -> match head with (a,b) -> f_comp_one tail size g@[m_ex_1 (a) (b) size];;

let f_one size = f_comp_one (f_iter (1) (1) size ([])) size ([]);;

let rec f_comp_two l size g = match l with
| [] -> g
| head :: tail -> match head with (a,b) -> f_comp_two tail size g@[m_ex_2 (a) (b) size];;

let f_two size = f_comp_two (f_iter (1) (1) size ([])) size ([]);;

let rec f_comp_three l size g = match l with
| [] -> g
| head :: tail -> match head with (a,b) -> f_comp_three tail size g@[m_ex_3 (a) (b) size];;

let f_three size = f_comp_three (f_iter (1) (1) size ([])) size ([]);;

let rec f_comp_four l size g = match l with
| [] -> g
| head :: tail -> match head with (a,b) -> f_comp_four tail size g@[m_ex_4 (a) (b) size];;

let f_four size = f_comp_four (f_iter (1) (1) size ([])) size ([]);;

let rec f_comp_five size l iter_x = if (iter_x = size-1) then l@[row_cond ((iter_x+1)*size-1) (iter_x*size)] else (f_comp_five (size) (l@[row_cond ((iter_x+1)*size-1) (iter_x*size)]) (iter_x+1));;

let f_five size = f_comp_five size ([]) (0);;

let get_all_bool_expr size = (f_one size)@(f_two size)@(f_three size)@(f_four size)@(f_five size);;

let rec string_list_x l iter_x size = if iter_x = size-1 then l@[string_of_int (size-1)] else string_list_x (l@[string_of_int (iter_x)]) (iter_x+1) (size);;

let rec gen_order size = string_list_x  ([]) (0) (size*size);;

let rec and_build l = match l with
| [x] -> x
| head :: tail -> Program.OprBinary(Program.AND,head,and_build tail);;

let solve_count size = let p = do_some size in BDD.sat_count (BDD.bddFromExpr (and_build (get_all_bool_expr size)) (gen_order size));;

let solve size = let p = do_some size in BDD.any_sat (BDD.bddFromExpr (and_build (get_all_bool_expr size)) (gen_order size));;

let rec conv_to_res l g size = match l with
| [] -> g
| head :: tail -> conv_to_res (tail) (g@[ String.concat (string_of_int(int_of_string (head) / size)) ["c"; string_of_int(int_of_string (head) mod size)]  ]) size
;;


let final_sol size = conv_to_res (solve size) ([]) size;;

let n_queen board_size = final_sol board_size ;;
