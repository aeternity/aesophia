%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc The Sophia lexer.
%%%
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_scan).

-export([scan/1, utf8_encode/1]).

-import(aeso_scan_lib, [token/1, token/2, symbol/0, skip/0,
                        override/2, push/2, pop/1]).

lexer() ->
    Number   = fun(Digit) -> [Digit, "+(_", Digit, "+)*"] end,
    DIGIT    = "[0-9]",
    HEXDIGIT = "[0-9a-fA-F]",
    LOWER    = "[a-z_]",
    UPPER    = "[A-Z]",
    CON      = [UPPER, "[a-zA-Z0-9_]*"],
    INT      = Number(DIGIT),
    HEX      = ["0x", Number(HEXDIGIT)],
    BYTES    = ["#", Number(HEXDIGIT)],
    WS       = "[\\000-\\ ]+",
    ID       = [LOWER, "[a-zA-Z0-9_']*"],
    TVAR     = ["'", ID],
    QID      = ["(", CON, "\\.)+", ID],
    QCON     = ["(", CON, "\\.)+", CON],
    OP       = "[=!<>+\\-*/:&|?~@^]+",
    %% Five cases for a character
    %%  * 1 7-bit ascii, not \ or '
    %%  * 2-4 8-bit values (UTF8)
    %%  * \ followed by a known modifier [aernrtv]
    %%  * \xhh
    %%  * \x{hhh...}
    CHAR     = "'(([\\x00-\\x26\\x28-\\x5b\\x5d-\\x7f])|([\\x00-\\xff][\\x80-\\xff]{1,3})|(\\\\[befnrtv'\\\\])|(\\\\x[0-9a-fA-F]{2,2})|(\\\\x\\{[0-9a-fA-F]*\\}))'",
    STRING   = "\"([^\"\\\\]|(\\\\.))*\"",

    CommentStart = {"/\\*", push(comment, skip())},
    CommentRules =
        [ CommentStart
        , {"\\*/",        pop(skip())}
        , {"[^/*]+|[/*]", skip()} ],

    Keywords = ["contract", "include", "let", "switch", "type", "record", "datatype", "if", "elif", "else", "function",
                "stateful", "payable", "true", "false", "mod", "public", "entrypoint", "private", "indexed", "namespace",
                "interface", "main", "using", "as", "for", "hiding", "band", "bor", "bxor", "bnot"
               ],
    KW = string:join(Keywords, "|"),

    Rules =
          %% Comments and whitespace
        [ CommentStart
        , {"//.*", skip()}
        , {WS,     skip()}

          %% Special characters
        , {"\\.\\.|[,.;()\\[\\]{}]", symbol()}

          %% Literals
        , {CHAR,   token(char,   fun parse_char/1)}
        , {STRING, token(string, fun parse_string/1)}
        , {HEX,    token(hex,    fun parse_hex/1)}
        , {INT,    token(int,    fun parse_int/1)}
        , {BYTES,  token(bytes,  fun parse_bytes/1)}

          %% Identifiers (qualified first!)
        , {QID,   token(qid,  fun(S) -> string:tokens(S, ".") end)}
        , {QCON,  token(qcon, fun(S) -> string:tokens(S, ".") end)}
        , {TVAR,  token(tvar)}
        , override({ID, token(id)}, {KW, symbol()})    %% Keywords override identifiers. Need to
        , {CON, token(con)}                            %% use override to avoid lexing "lettuce"
                                                       %% as ['let', {id, "tuce"}].
          %% Operators
        , {OP, symbol()}
        ],

    [{code, Rules}, {comment, CommentRules}].

scan(String) ->
    Lexer = aeso_scan_lib:compile(lexer()),
    aeso_scan_lib:string(Lexer, code, String).

%% -- Helpers ----------------------------------------------------------------

parse_string([$" | Chars]) ->
    unicode:characters_to_nfc_binary(unescape(Chars)).

parse_char([$' | Chars]) ->
    case unicode:characters_to_nfc_list(unescape($', Chars, [])) of
        [Char] -> Char;
        _Bad   -> {error, "Bad character literal: '" ++ Chars}
    end.

utf8_encode(Cs) ->
    binary_to_list(unicode:characters_to_binary(Cs)).

unescape(Str) -> unescape($", Str, []).

unescape(Delim, [Delim], Acc) ->
    list_to_binary(lists:reverse(Acc));
unescape(Delim, [$\\, $x, ${ | Chars ], Acc) ->
    {Ds, [_ | Cs]} = lists:splitwith(fun($}) -> false ; (_) -> true end, Chars),
    C = list_to_integer(Ds, 16),
    Utf8Cs = binary_to_list(unicode:characters_to_binary([C])),
    unescape(Delim, Cs, [Utf8Cs | Acc]);
unescape(Delim, [$\\, $x, D1, D2 | Chars ], Acc) ->
    C = list_to_integer([D1, D2], 16),
    Utf8Cs = binary_to_list(unicode:characters_to_binary([C])),
    unescape(Delim, Chars, [Utf8Cs | Acc]);
unescape(Delim, [$\\, Code | Chars], Acc) ->
    Ok = fun(C) -> unescape(Delim, Chars, [C | Acc]) end,
    case Code of
        Delim -> Ok(Delim);
        $\\ -> Ok($\\);
        $b  -> Ok($\b);
        $e  -> Ok($\e);
        $f  -> Ok($\f);
        $n  -> Ok($\n);
        $r  -> Ok($\r);
        $t  -> Ok($\t);
        $v  -> Ok($\v);
        _   -> error("Bad control sequence: \\" ++ [Code])  %% TODO
    end;
unescape(Delim, [C | Chars], Acc) ->
    unescape(Delim, Chars, [C | Acc]).

strip_underscores(S) ->
    lists:filter(fun(C) -> C /= $_ end, S).

parse_hex("0x" ++ S) ->
    list_to_integer(strip_underscores(S), 16).

parse_int(S) ->
    list_to_integer(strip_underscores(S)).

parse_bytes("#" ++ S0) ->
    S      = strip_underscores(S0),
    N      = list_to_integer(S, 16),
    Digits = (length(S) + 1) div 2,
    <<N:Digits/unit:8>>.

