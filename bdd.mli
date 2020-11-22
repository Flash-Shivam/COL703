open Formula;;
module BDD : sig
		type sat_assignment = string list

		(* define the type robdd as per your code. This type 
		is used as ROBDD in all of the functions *)
		type robdd = int ;;

		exception Not_implemented

		(* Creates ROBDD from a boolean expression.
		Program.bool_expr defines boolean expression.
		string list is ordered list of variables that represents
		the ordering to be considered while making ROBDD *)
		val bddFromExpr : Program.bool_expr -> string list -> robdd

		(* Counts and returns number of satisfying assignemnts of a ROBDD *)
		val sat_count: robdd -> int

		(* Returns all possible satisfying assignemnts of a ROBDD *)
		val all_sat: robdd -> sat_assignment list

		(* Returns one possible satisfying assignemnts of a ROBDD *)
		val any_sat: robdd -> sat_assignment

		(* Generate the dot file for bdd and write it to file named
		bdd.dot *)
		val to_dot : robdd -> unit
end ;;
