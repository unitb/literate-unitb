note
	description: "Summary description for {ERROR_MESSAGE}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	ERROR_MESSAGE

inherit
	ANY
		redefine
			default_create
		end

feature {NONE} -- Initialization

	default_create
		do
			file_name := ""
			message := ""
		end

feature -- Access

	file_name: STRING assign set_file_name

	message: STRING assign set_message

	line: INTEGER assign set_line

	column: INTEGER assign set_column

	list_row: EV_MULTI_COLUMN_LIST_ROW
		do
			create Result
			Result.extend (line.out)
			Result.extend (message)
			Result.pointer_double_press_actions.extend (agent on_select)
		end

	tree_node: EV_TREE_NODE
		do
			create {EV_TREE_ITEM} Result
			Result.set_text (message)
			Result.pointer_double_press_actions.extend (agent on_select )
		end

	on_select (x: INTEGER_32; y: INTEGER_32;
			button: INTEGER_32;
			x_tilt: REAL_64; y_tilt: REAL_64;
			pressure: REAL_64;
			screen_x: INTEGER_32; screen_y: INTEGER_32)
		local
			env: EXECUTION_ENVIRONMENT
		do
			create env
			env.launch ("texstudio " + file_name + " -line " + line.out)
--			io.put_string ("Click: " + message)
--			io.put_new_line
		end

feature -- Element change

	set_file_name (a_fn: STRING)
			-- `set_file_name'
		do
			file_name := a_fn
		end

	set_message (a_msg: STRING)
			-- `set_file_name'
		do
			message := a_msg
		end

	set_line (a_ln: INTEGER)
			-- `set_file_name'
		do
			line := a_ln
		end

	set_column (a_col: INTEGER)
			-- `set_file_name'
		do
			column := a_col
		end

end
