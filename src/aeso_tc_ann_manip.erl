-module(aeso_tc_ann_manip).

-export([ pos/1
        , pos/2
        , loc/1
        ]).

src_file(T)      -> aeso_syntax:get_ann(file, T, no_file).
include_type(T)  -> aeso_syntax:get_ann(include_type, T, none).
line_number(T)   -> aeso_syntax:get_ann(line, T, 0).
column_number(T) -> aeso_syntax:get_ann(col, T, 0).

pos(T)    -> aeso_errors:pos(src_file(T), line_number(T), column_number(T)).
pos(L, C) -> aeso_errors:pos(L, C).

loc(T) ->
    {src_file(T), include_type(T), line_number(T), column_number(T)}.
