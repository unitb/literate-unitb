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
		do
			init
			map := new_map
		end

	map: POINTER

	item alias "[]" (i: INTEGER): INTEGER assign set_item
		do
			Result := image (map, i)
		end

	set_item (i, j: INTEGER)
		do
			set (map, j, i)
		end

	new_error_list: LIST [ERROR_MESSAGE]
		local
			p: POINTER
			l_msg: ERROR_MESSAGE
		do
			from
				p := error_list
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
			free_list (p)
		end

feature -- C wrappers

	init
		once
			lib_init
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
				    hs_add_root(__stginit_Safe);
				}
		]"
		end

	new_map: POINTER
		external
			"C (): EIF_INTEGER  | %"haskell.h%""
		end

	image (x: POINTER; n: INTEGER): INTEGER
		external
			"C (HsStablePtr, EIF_INTEGER): EIF_INTEGER  | %"haskell.h%""
		end

	set (x: POINTER; i,j: INTEGER)
		external
			"C (HsStablePtr, EIF_INTEGER, EIF_INTEGER) | %"haskell.h%""
		end

	free_map (p : POINTER)
		external
			"C (HsStablePtr) | %"haskell.h%""
		end

	file_name (p: POINTER): STRING
		external
			"C inline use  %"haskell.h%""
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
			"C inline use  %"haskell.h%""
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
			"C (void*): int | %"haskell.h%""
		alias
			"get_line_number"
		end

	error_list: POINTER
		external
			"C (): (void*) | %"haskell.h%""
		end

	free_list (p: POINTER)
		external
			"C (void*) | %"haskell.h%""
		alias
			"free_map"
		end

	move_forward (p: POINTER)
		require
			not off (p)
		external
			"C (void*) | %"haskell.h%""
		end

	off (p: POINTER): BOOLEAN
		external
			"C (void*): HsBool | %"haskell.h%""
		end


	dispose
		do
			free_map (map)
		end

end
