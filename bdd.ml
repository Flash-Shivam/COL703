open Graph;;
open Formula;;
module BDD = struct
		type sat_assignment = string list

		(* define the type robdd in whatever way you want  *)
		type robdd = int ;;

		exception Not_implemented


(*		let bddFromExpr bexpr order = f_robdd_prime (bexpr) order  ;;


		let sat_count bdd = f_count bdd ;;
		let all_sat bdd = f_asat bdd ;;
		let any_sat bdd =  f_sat bdd ;;


		let to_dot bdd = raise Not_implemented;;*)


		exception Cant_be_evaluated
		exception No_valid_assingment
		let rec feval bexpr bassign = match bexpr with
		| Program.Constant(false) -> 0
		| Program.OprUnary(Program.NOT,a) -> if ((feval a bassign) =1) then 0 else 1
		| Program.Variable(x) -> if (List.mem x bassign) then 1 else raise Cant_be_evaluated
		| Program.Constant(true) -> 1
		| Program.OprBinary(Program.AND,a,b) -> if ( (feval a bassign) = 0 || (feval b bassign) = 0) then 0 else (feval a bassign) * (feval b bassign)
		| Program.OprBinary(Program.OR,a,b) -> if ( (feval a bassign) = 1 || (feval b bassign) = 1) then 1 else 0;
		| Program.OprBinary(Program.IFTHEN,a,b) -> if((feval a bassign) = 0 || (feval b bassign) = 1) then 1 else 0
		| Program.OprBinary(Program.IFF,a,b) -> if((feval a bassign) = (feval b bassign)) then 1 else 0
		| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> if((feval a bassign) = 1) then (feval b bassign) else (feval c bassign)
		;;

		let rec feval_prime bexpr bassign = match bexpr with
		| Program.Constant(false) -> 0
		| Program.OprUnary(Program.NOT,a) -> if ((feval_prime a bassign) =1) then 0 else 1
		| Program.Variable(x) -> if (List.mem x bassign) then 1 else 0
		| Program.Constant(true) -> 1
		| Program.OprBinary(Program.AND,a,b) -> if ( (feval_prime a bassign) = 0 || (feval_prime b bassign) = 0) then 0 else 1
		| Program.OprBinary(Program.OR,a,b) -> if ( (feval_prime a bassign) = 1 || (feval_prime b bassign) = 1) then 1 else 0;
		| Program.OprBinary(Program.IFTHEN,a,b) -> if((feval_prime a bassign) = 0 || (feval_prime b bassign) = 1) then 1 else 0
		| Program.OprBinary(Program.IFF,a,b) -> if((feval_prime a bassign) = (feval_prime b bassign)) then 1 else 0
		| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> if((feval_prime a bassign) = 1) then (feval_prime b bassign) else (feval_prime c bassign)
		;;


		let safe_fval bexpr = try feval bexpr ([]) with Cant_be_evaluated -> -1;;

		let rec substitute_x bexpr var_x bool_x = match bexpr with
		| Program.Variable(x) -> if (x = var_x) then (if bool_x then Program.Constant(true) else Program.Constant(false)) else Program.Variable(x)
		| Program.OprUnary(Program.NOT,a) -> Program.OprUnary(Program.NOT,substitute_x a var_x bool_x)
		| Program.OprBinary(z,a,b) -> Program.OprBinary(z,substitute_x a var_x bool_x,substitute_x b var_x bool_x)
		| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> Program.OprTernary(Program.IFTHENELSE,substitute_x a var_x bool_x,substitute_x b var_x bool_x,substitute_x c var_x bool_x)
		| z -> z;;


		let rec conv_ifte bexpr = match bexpr with
		| Program.OprUnary(Program.NOT,a) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),Program.Constant(false),Program.Constant(true))
		| Program.OprBinary(Program.AND,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),Program.Constant(false))
		| Program.OprBinary(Program.OR,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),Program.Constant(true),(conv_ifte b))
		| Program.OprBinary(Program.IFTHEN,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),Program.Constant(true))
		| Program.OprBinary(Program.IFF,a,b) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),(conv_ifte (Program.OprUnary(Program.NOT,b))))
		| Program.OprTernary(Program.IFTHENELSE,a,b,c) -> Program.OprTernary(Program.IFTHENELSE,(conv_ifte a),(conv_ifte b),(conv_ifte c))
		| a -> a
		;;


		let table = Hashtbl.create 1000;;
		let table2 = Hashtbl.create 1000;;
		let var_table = Hashtbl.create 1000;;




		let mk index low high = if (low = high) then low else if (Hashtbl.mem table2 (index,low,high)) then Hashtbl.find table2 (index,low,high) else let p = Hashtbl.length table in let z = Hashtbl.add table (p) (index,low,high) in let y = Hashtbl.add table2 (index,low,high) (p) in (p);;


		let rec robddFromExpr_prime bexpr order num index l = if (index > num) then feval_prime bexpr l  else match order with
		| head :: tail -> (mk index (robddFromExpr_prime (bexpr) (tail) (num) (index+1) (l)) (robddFromExpr_prime (bexpr) (tail) (num) (index+1) (l@[Hashtbl.find var_table (index)])));;

		let rec robddFromExpr bexpr order num index = if (index > num) then safe_fval bexpr else match order with
		| head :: tail -> (mk index (robddFromExpr (substitute_x (bexpr) (head) (false)) tail num (index+1)) (robddFromExpr (substitute_x (bexpr) (head) (true)) tail num (index+1)));;

		let rec power x n = if n = 0 then 1 else if n = 1 then x else x * (power x (n-1));;

		let get_low node = match (Hashtbl.find table node) with
		| (a,b,c) -> b;;

		let get_high node = match (Hashtbl.find table node) with
		| (a,b,c) -> c;;

		let get_var node = match (Hashtbl.find table node) with
		| (a,b,c) -> a;;

		let rec count_sat node = if (node = 0) then 0 else if (node = 1) then 1 else (power (2) (get_var (get_low node) - (get_var node) -1 ))*(count_sat (get_low node)) + (power (2) (get_var (get_high node) - (get_var node) -1 )  )*(count_sat (get_high node));;


		let f_count node = (power (2) ((get_var node)-1)) * (count_sat node);;


		let rec fill_var_table order num = match order with
		| [x] -> Hashtbl.add var_table (num) (x)
		| head :: tail -> let p = Hashtbl.add var_table (num) (head) in fill_var_table tail (num + 1);;

		let f_robdd bexpr order = let f = Hashtbl.clear var_table in let v = fill_var_table order (1) in let r = Hashtbl.clear table in let t = Hashtbl.clear table2 in let m = Hashtbl.add table (0) (List.length order+1,-1,-1) in let n = Hashtbl.add table (1) (List.length order+1,-1,-1) in robddFromExpr bexpr order (List.length order) (1);;

		let f_robdd_prime bexpr order = let f = Hashtbl.clear var_table in let v = fill_var_table order (1) in let r = Hashtbl.clear table in let t = Hashtbl.clear table2 in let m = Hashtbl.add table (0) (List.length order+1,-1,-1) in let n = Hashtbl.add table (1) (List.length order+1,-1,-1) in robddFromExpr_prime bexpr order (List.length order) (1) ([]);;

		let rec f_any_sat node list_l = if node = 0 then raise No_valid_assingment else if node = 1 then list_l else if ((get_low node) = 0) then f_any_sat (get_high node) (list_l@[(Hashtbl.find var_table (get_var node))]) else  f_any_sat (get_low node) (list_l);;

		let f_sat node = f_any_sat node ([]);;

		let rec add_var node list_l list_p = match list_l with
		| [] -> list_p@[[Hashtbl.find var_table (node)]]
		| head :: tail -> add_var node tail (list_p@[head@[Hashtbl.find var_table (node)]]);;

		let rec f_all_sat node list_of_l = if node = 0 then (list_of_l@[["-1";]]) else if node = 1 then (list_of_l@[]) else list_of_l@(f_all_sat (get_low node) (list_of_l))@(add_var (get_var node) (f_all_sat (get_high node) list_of_l) ([]));;

		let f_asat node = f_all_sat node ([]);;



		let rec get_val_list l size start = if (start = size) then (l@[size]) else (if (Hashtbl.mem table start) then (get_val_list (l@[start]) size (start+1)) else (get_val_list l size (start+1)));;

		(*let z = f_robdd_prime (Program.OprBinary(Program.AND,Program.OprBinary(Program.IFF,Program.Variable("a"),Program.Variable("b")),Program.OprBinary(Program.IFF,Program.Variable("c"),Program.Variable("d")))) (["a";"c";"b";"d";]);;*)
		(*let init_table  =  get_val_list ([]) (z) 2 ;;*)
		let rec print_list_of_int l = match l with
		| [x] -> print_int x
		| head :: tail -> print_int head;print_list_of_int tail;;


		module Node = struct
		   type t = int
		   let compare = Pervasives.compare
		   let hash = Hashtbl.hash
		   let equal = (=)
		end          ;;

		module Edge = struct
		   type t = string
		   let compare = Pervasives.compare
		   let equal = (=)
		   let default = ""
		end
		;;

		module G =  Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
		let g = G.empty


		let rec make_edges l g = match l with
		| [x] -> (match Hashtbl.find table x with | (a,b,c) -> let g = G.add_edge g x b in G.add_edge g x c)
		| head :: tail ->( match (Hashtbl.find table (head)) with | (a,b,c) -> let g = G.add_edge g (head) (b) in let g = G.add_edge g (head) (c) in (make_edges tail g))
		;;

		module Dot = Graph.Graphviz.Dot(struct
		   include G (* use the graph module from above *)
		   let edge_attributes (_, e, _) = [`Label e; `Color 4711]
		   let default_edge_attributes _ = []
		   let get_subgraph _ = None
		   let vertex_attributes _ = [`Shape `Box]
		   let vertex_name v = string_of_int v
		   let default_vertex_attributes _ = []
		  let graph_attributes _ = []
		end);;

		let make_dot bdd = let init_tab  =  get_val_list ([]) (bdd) 2 in let g = make_edges init_tab g in
		   let file = open_out_bin "bdd.dot" in
		   Dot.output_graph file g;;


			 let bddFromExpr bexpr order = f_robdd_prime (bexpr) order  ;;


			 		let sat_count bdd = f_count bdd ;;
			 		let all_sat bdd = f_asat bdd ;;
			 		let any_sat bdd =  f_sat bdd ;;


		let to_dot bdd = make_dot bdd;;

		let s_prime = f_robdd (Program.OprBinary(Program.OR,Program.Variable("a"),Program.Variable("b"))) (["a";"b";]);;

		let rec iterate_hash size start l = if (start = size) then (match Hashtbl.find table start with | (a,b,c) -> if List.mem (Hashtbl.find var_table a) l then l else (l@[Hashtbl.find var_table a]) ) else (match Hashtbl.find table start with | (a,b,c) -> if List.mem (Hashtbl.find var_table a) l then iterate_hash size (start+1) l else iterate_hash size (start+1) (l@[Hashtbl.find var_table a]) ) ;;
		let rec get_all_vars start l = if (start = Hashtbl.length var_table) then l@[Hashtbl.find var_table start] else get_all_vars (start+1) l@[Hashtbl.find var_table start];;
		let rec trim_l l1 l2 h = match l1 with
		| [x] -> if List.mem x l2 then h else h@[x]
		| head :: tail -> if List.mem head l2 then trim_l tail l2 h else trim_l tail l2 h@[head];;
		print_int s_prime;;
		let p = match Hashtbl.find table 2 with (a,b,c) -> a;;
		print_int p;;
		print_string (Hashtbl.find var_table p);;

		let rec subset l =
			match l with
			| [] -> [[]]
			| (h::tl) ->
									let second = subset tl in
									List.append (List.map (fun x -> h::x) second) second;;

		let rec remove_x l y = match l with
		| [] -> []
		| [x] -> if List.mem "-1" x then y else y@[x]
		| head :: tail -> if List.mem "-1" head then (remove_x tail y) else (remove_x tail y@[head]);;

		let rec comb_l l h j= match h with
		| [x] -> j@[l@x]
		| head :: tail -> comb_l l tail j@[l@head];;

		let rec combine_list l1 l2 y = match l2 with
		| [x] -> y@(comb_l x l1 [])
		| head :: tail -> combine_list l1 tail y@(comb_l head l1 []) ;;
		let y_prime = trim_l (get_all_vars 1 ([])) (iterate_hash s_prime 2 ([])) ([]);;
		let list_un = subset (y_prime);;
		let list_imp = remove_x (f_asat s_prime) ([]);;

		let z = combine_list list_imp list_un ([]);;

		let rec print_list_x l = match l with
		| [x] -> print_string x; print_string ";"
		| head :: tail -> print_string head;print_string ";";print_list_x tail;;

		let rec print_l_l l = match l with
		| [x] -> print_list_x x;print_string "\n"
		| head :: tail -> print_list_x head;print_string "\n";print_l_l tail;;

		let y = print_l_l z;;

		print_string "\n***\n";;

		print_list_x (iterate_hash s_prime 2 ([]));;
		print_string "\n";
		print_string "\n***\n";;
		print_l_l list_imp;;
		print_string "\n***\n";;
		print_l_l (f_asat s_prime);;

end  ;;

(* let a = (Program.Constant true);;
a;;*)


(*@f_all_sat (get_high node) (add_var (get_var node) list_of_l ([]))*)
