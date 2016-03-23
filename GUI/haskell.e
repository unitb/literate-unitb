note
	description: "Summary description for {HASKELL}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	HASKELL

inherit
	DISPOSABLE
		redefine
			default_create,
			dispose
		end

feature

	default_create
		local
			l_str: C_STRING
		do
			create l_str.make ("Tests/train-station.tex")
			lib_init
			verifier := run_verifier (l_str.item)
--			map := new_map
		end

--	map: POINTER

--	item alias "[]" (i: INTEGER): INTEGER assign set_item
--		do
--			Result := image (map, i)
--		end

--	set_item (i, j: INTEGER)
--		do
--			set (map, j, i)
--		end

	new_error_list: LIST [ERROR_MESSAGE]
		local
			p: POINTER
		do
			p := get_error_list (verifier)
			Result := as_error_list (p)
			free_list (p)
		end

	failed_proof_obligations: LIST [ERROR_MESSAGE]
		local
			p: POINTER
		do
			p := get_proof_obligations (verifier)
			Result := as_error_list (p)
			free_list (p)
		end

feature {NONE} -- C wrappers

	verifier: POINTER

--	init
--		once
--			lib_init
--		end

	as_error_list (p: POINTER): LIST [ERROR_MESSAGE]
		local
			l_msg: ERROR_MESSAGE
		do
			from
				create {ARRAYED_LIST [ERROR_MESSAGE]} Result.make (10)
			until
				off (p)
			loop
				create l_msg
				l_msg.file_name := file_name (p)
				l_msg.message := message (p)
				l_msg.line := line_number (p)
				Result.extend (l_msg)
				move_forward (p)
			end
		end

	lib_init -- (x, y: POINTER)
		external
--			"C (int *, char ***) | %"hsffi.h%""
			"C inline use   %"haskell.h%""
		alias
--			"hs_init"
			"[
				{	
				    int argc = 0;
				    
				    hs_init(&argc, NULL);
				    // hs_add_root(__stginit_Browser);
				    hs_add_root(__stginit_Pipeline);
				}
		]"
		end

	lib_final
		external
			"C inline use %"haskell.h%""
		alias
			"[
				hs_exit();
				]"
		end

--	new_map: POINTER
--		external
--			"C (): EIF_INTEGER  | %"browser_stub.h%""
--		end

--	image (x: POINTER; n: INTEGER): INTEGER
--		external
--			"C (HsStablePtr, EIF_INTEGER): EIF_INTEGER  | %"browser_stub.h%""
--		end

--	set (x: POINTER; i,j: INTEGER)
--		external
--			"C (HsStablePtr, EIF_INTEGER, EIF_INTEGER) | %"browser_stub.h%""
--		end

--	free_map (p : POINTER)
--		external
--			"C (HsStablePtr) | %"browser_stub.h%""
--		end

	file_name (p: POINTER): STRING
		external
			"C inline use  %"browser_stub.h%""
		alias
			"[
				{
					char *ptr;
					EIF_REFERENCE r;
					ptr = get_file_name ($p);
					r = eif_string (ptr);
					free (ptr);
					return r;
				}
			]"
		end

	message (p: POINTER): STRING
		external
			"C inline use  %"browser_stub.h%""
		alias
			"[
				{
					char *ptr;
					EIF_REFERENCE r;
					ptr = get_message ($p);
					r = eif_string (ptr);
					free (ptr);
					return r;
				}
			]"
		end

	line_number (p: POINTER): INTEGER
		external
			"C (void*): int | %"browser_stub.h%""
		alias
			"get_line_number"
		end

	error_list: POINTER
		external
			"C (): (void*) | %"browser_stub.h%""
		end

--	get_error_list (p: POINTER): POINTER
--		external
--			"C (void*): (void*) | %"pipeline_stub.h%""
--		end

	free_list (p: POINTER)
		external
			"C (void*) | %"browser_stub.h%""
		alias
			"free_list"
		end

	move_forward (p: POINTER)
		require
			not off (p)
		external
			"C (void*) | %"browser_stub.h%""
		end

	off (p: POINTER): BOOLEAN
		external
			"C (void*): HsBool | %"browser_stub.h%""
		end

	run_verifier (p: POINTER): POINTER
		external
			"C (char*): (void *) | %"cpipeline_stub.h%""
		end

	get_error_list (v: POINTER): POINTER
		external
			"C (void *): (void *) | %"cpipeline_stub.h%""
		end

	get_proof_obligations (v: POINTER): POINTER
		external
			"C (void *): (void *) | %"cpipeline_stub.h%""
		end

	dispose
		do
			lib_final
		end

end
