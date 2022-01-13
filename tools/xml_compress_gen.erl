%% File    : xml_compress_gen.erl
%% Author  : Pawel Chmielowski
%% Purpose :
%% Created :  14 Sep 2018 Pawel Chmielowski
%%
%%
%% ejabberd, Copyright (C) 2002-2020  ProcessOne
%%
%% This program is free software; you can redistribute it and/or
%% modify it under the terms of the GNU General Public License as
%% published by the Free Software Foundation; either version 2 of the
%% License, or (at your option) any later version.
%%
%% This program is distributed in the hope that it will be useful,
%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
%% General Public License for more details.
%%
%% You should have received a copy of the GNU General Public License along
%% with this program; if not, write to the Free Software Foundation, Inc.,
%% 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
%%

-module(xml_compress_gen).
-author("pawel@process-one.net").

-include("xmpp.hrl").

%% API
-export([archive_analyze/3, process_stats/1, gen_code/3]).

-record(el_stats, {count = 0, empty_count = 0, only_text_count = 0, attrs = #{}, text_stats = #{}}).
-record(attr_stats, {count = 0, vals = #{}}).

archive_analyze(Host, Table, EHost) ->
    case ejabberd_sql:sql_query(Host, [<<"select username, peer, kind, xml from ", Table/binary>>]) of
	{selected, _, Res} ->
	    lists:foldl(
		fun([U, P, K, X], Stats) ->
		    M = case K of
			    <<"groupchat">> ->
				U;
			    _ ->
				<<U/binary, "@", EHost/binary>>
			end,
		    El = fxml_stream:parse_element(X),
		    analyze_element({El, <<"stream">>, <<"jabber:client">>, M, P}, Stats)
		end, {0, #{}}, Res);
	_ ->
	    none
    end.

encode_id(Num) when Num < 64 ->
    iolist_to_binary(io_lib:format("~p:8", [Num])).

gen_code(_File, _Rules, $<) ->
    {error, <<"Invalid version">>};
gen_code(File, Rules, Ver) when Ver < 64 ->
    {Data, _} = lists:foldl(
	     fun({Ns, El, Attrs, Text}, {Acc, Id}) ->
	    NsC = case lists:keyfind(Ns, 1, Acc) of
		      false -> [];
		      {_, L} -> L
		  end,
	    {AttrsE, _} = lists:mapfoldl(
		fun({AName, AVals}, Id2) ->
		    {AD, Id3} = lists:mapfoldl(
			fun(AVal, Id3) ->
			    {{AVal, encode_id(Id3)}, Id3 + 1}
			end, Id2, AVals),
		    {{AName, AD ++ [encode_id(Id3)]}, Id3 + 1}
		end, 3, Attrs),
	    {TextE, Id5} = lists:mapfoldl(
		fun(TextV, Id4) ->
		    {{TextV, encode_id(Id4)}, Id4 + 1}
		end, Id + 1, Text),
	    {lists:keystore(Ns, 1, Acc, {Ns, NsC ++ [{El, encode_id(Id), AttrsE, TextE}]}), Id5}
	end, {[], 5}, Rules),
    {ok, Dev} = file:open(File, [write]),
    Mod = filename:basename(File, ".erl"),
    io:format(Dev, "-module(~s).~n-export([encode/3, decode/3]).~n~n", [Mod]),
    RulesS = iolist_to_binary(io_lib:format("~p", [Rules])),
    RulesS2 = binary:replace(RulesS, <<"\n">>, <<"\n%  ">>, [global]),
    io:format(Dev, "% This file was generated by xml_compress_gen~n%~n"
		   "% Rules used:~n%~n%  ~s~n~n", [RulesS2]),
    VerId = iolist_to_binary(io_lib:format("~p:8", [Ver])),
    gen_encode(Dev, Data, VerId),
    gen_decode(Dev, Data, VerId),
    file:close(Dev),
    Data.

gen_decode(Dev, Data, VerId) ->
    io:format(Dev, "decode(<<$<, _/binary>> = Data, _J1, _J2) ->~n"
		   "  fxml_stream:parse_element(Data);~n"
		   "decode(<<~s, Rest/binary>>, J1, J2) ->~n"
		   "  {El, _} = decode(Rest, <<\"jabber:client\">>, J1, J2),~n"
		   "  El.~n~n", [VerId]),
    io:format(Dev, "decode_string(Data) ->~n"
		   "  case Data of~n"
		   "    <<0:2, L:6, Str:L/binary, Rest/binary>> ->~n"
		   "      {Str, Rest};~n"
		   "    <<1:2, L1:6, 0:2, L2:6, Rest/binary>> ->~n"
		   "      L = L2*64 + L1,~n"
		   "    <<Str:L/binary, Rest2/binary>> = Rest,~n"
		   "      {Str, Rest2};~n"
		   "    <<1:2, L1:6, 1:2, L2:6, L3:8, Rest/binary>> ->~n"
		   "      L = (L3*64 + L2)*64 + L1,~n"
		   "    <<Str:L/binary, Rest2/binary>> = Rest,~n"
		   "      {Str, Rest2}~n"
		   "  end.~n~n", []),
    io:format(Dev, "decode_child(<<1:8, Rest/binary>>, _PNs, _J1, _J2) ->~n"
		   "  {Text, Rest2} = decode_string(Rest),~n"
		   "  {{xmlcdata, Text}, Rest2};~n", []),
    io:format(Dev, "decode_child(<<2:8, Rest/binary>>, PNs, J1, J2) ->~n"
		   "  {Name, Rest2} = decode_string(Rest),~n"
		   "  {Attrs, Rest3} = decode_attrs(Rest2),~n"
		   "  {Children, Rest4} = decode_children(Rest3, PNs, J1, J2),~n"
		   "  {{xmlel, Name, Attrs, Children}, Rest4};~n", []),
    io:format(Dev, "decode_child(<<3:8, Rest/binary>>, PNs, J1, J2) ->~n"
		   "  {Ns, Rest2} = decode_string(Rest),~n"
		   "  {Name, Rest3} = decode_string(Rest2),~n"
		   "  {Attrs, Rest4} = decode_attrs(Rest3),~n"
		   "  {Children, Rest5} = decode_children(Rest4, Ns, J1, J2),~n"
		   "  {{xmlel, Name, add_ns(PNs, Ns, Attrs), Children}, Rest5};~n", []),
    io:format(Dev, "decode_child(<<4:8, Rest/binary>>, _PNs, _J1, _J2) ->~n"
		   "  {stop, Rest};~n", []),
    io:format(Dev, "decode_child(Other, PNs, J1, J2) ->~n"
		   "  decode(Other, PNs, J1, J2).~n~n", []),
    io:format(Dev, "decode_children(Data, PNs, J1, J2) ->~n"
		   "  prefix_map(fun(Data2) -> decode(Data2, PNs, J1, J2) end, Data).~n~n", []),
    io:format(Dev, "decode_attr(<<1:8, Rest/binary>>) ->~n"
		   "  {Name, Rest2} = decode_string(Rest),~n"
		   "  {Val, Rest3} = decode_string(Rest2),~n"
		   "  {{Name, Val}, Rest3};~n", []),
    io:format(Dev, "decode_attr(<<2:8, Rest/binary>>) ->~n"
		   "  {stop, Rest}.~n~n", []),
    io:format(Dev, "decode_attrs(Data) ->~n"
		   "  prefix_map(fun decode_attr/1, Data).~n~n", []),
    io:format(Dev, "prefix_map(F, Data) ->~n"
		   "  prefix_map(F, Data, []).~n~n", []),
    io:format(Dev, "prefix_map(F, Data, Acc) ->~n"
		   "  case F(Data) of~n"
		   "    {stop, Rest} ->~n"
		   "      {lists:reverse(Acc), Rest};~n"
		   "    {Val, Rest} ->~n"
		   "      prefix_map(F, Rest, [Val | Acc])~n"
		   "  end.~n~n", []),
    io:format(Dev, "add_ns(Ns, Ns, Attrs) ->~n"
		   "  Attrs;~n"
		   "add_ns(_, Ns, Attrs) ->~n"
		   "  [{<<\"xmlns\">>, Ns} | Attrs].~n~n", []),
    lists:foreach(
	fun({Ns, Els}) ->
	    lists:foreach(
		fun({Name, Id, Attrs, Text}) ->
		    io:format(Dev, "decode(<<~s, Rest/binary>>, PNs, J1, J2) ->~n"
				   "  Ns = ~p,~n", [Id, Ns]),
		    case Attrs of
			[] ->
			    io:format(Dev, "  {Attrs, Rest2} = decode_attrs(Rest),~n", []);
			_ ->
			    io:format(Dev, "  {Attrs, Rest2} = prefix_map(fun~n", []),
			    lists:foreach(
				fun({AName, AVals}) ->
				    lists:foreach(
					fun({j1, AId}) ->
					    io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							   "      {{~p, J1}, Rest3};~n", [AId, AName]);
					   ({j2, AId}) ->
					       io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							      "      {{~p, J2}, Rest3};~n", [AId, AName]);
					   ({{j1}, AId}) ->
					       io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							      "      {AVal, Rest4} = decode_string(Rest3),~n"
							      "      {{~p, <<J1/binary, AVal/binary>>}, Rest4};~n",
							 [AId, AName]);
					   ({{j2}, AId}) ->
					       io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							      "      {AVal, Rest4} = decode_string(Rest3),~n"
							      "      {{~p, <<J2/binary, AVal/binary>>}, Rest4};~n",
							 [AId, AName]);
					   ({AVal, AId}) ->
					       io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							      "      {{~p, ~p}, Rest3};~n",
							 [AId, AName, AVal]);
					   (AId) ->
					       io:format(Dev, "    (<<~s, Rest3/binary>>) ->~n"
							      "      {AVal, Rest4} = decode_string(Rest3),~n"
							      "      {{~p, AVal}, Rest4};~n",
							 [AId, AName])
					end, AVals)
				end, Attrs),
			    io:format(Dev, "    (<<2:8, Rest3/binary>>) ->~n"
					   "      {stop, Rest3};~n"
					   "    (Data) ->~n"
					   "      decode_attr(Data)~n"
					   "  end, Rest),~n", [])
		    end,
		    case Text of
			[] ->
			    io:format(Dev, "  {Children, Rest6} = decode_children(Rest2, Ns, J1, J2),~n", []);
			_ ->
			    io:format(Dev, "  {Children, Rest6} = prefix_map(fun", []),
			    lists:foreach(
				fun({TextS, TId}) ->
				    io:format(Dev, "    (<<~s, Rest5/binary>>) ->~n"
						   "      {{xmlcdata, ~p}, Rest5};~n",
					      [TId, TextS])
				end, Text),

			    io:format(Dev, "    (Other) ->~n"
					   "      decode_child(Other, Ns, J1, J2)~n"
					   "  end, Rest2),~n", [])
		    end,
		    io:format(Dev, "  {{xmlel, ~p, add_ns(PNs, Ns, Attrs), Children}, Rest6};~n", [Name])
		end, Els)
	end, Data),
    io:format(Dev, "decode(Other, PNs, J1, J2) ->~n"
		   "  decode_child(Other, PNs, J1, J2).~n~n", []).


gen_encode(Dev, Data, VerId) ->
    io:format(Dev, "encode(El, J1, J2) ->~n"
		   "  encode_child(El, <<\"jabber:client\">>,~n"
		   "    J1, J2, byte_size(J1), byte_size(J2), <<~s>>).~n~n", [VerId]),
    io:format(Dev, "encode_attr({<<\"xmlns\">>, _}, Acc) ->~n"
		   "  Acc;~n"
		   "encode_attr({N, V}, Acc) ->~n"
		   "  <<Acc/binary, 1:8, (encode_string(N))/binary,~n"
		   "    (encode_string(V))/binary>>.~n~n", []),
    io:format(Dev, "encode_attrs(Attrs, Acc) ->~n"
		   "  lists:foldl(fun encode_attr/2, Acc, Attrs).~n~n", []),
    io:format(Dev, "encode_el(PNs, Ns, Name, Attrs, Children, J1, J2, J1L, J2L, Pfx) ->~n"
		   "  E1 = if~n"
		   "    PNs == Ns -> encode_attrs(Attrs, <<Pfx/binary, 2:8, (encode_string(Name))/binary>>);~n"
		   "    true -> encode_attrs(Attrs, <<Pfx/binary, 3:8, "
		   "(encode_string(Ns))/binary, (encode_string(Name))/binary>>)~n"
		   "  end,~n"
		   "  E2 = encode_children(Children, Ns, J1, J2, J1L, J2L, <<E1/binary, 2:8>>),~n"
		   "  <<E2/binary, 4:8>>.~n~n", []),
    io:format(Dev, "encode_child({xmlel, Name, Attrs, Children}, PNs, J1, J2, J1L, J2L, Pfx) ->~n"
		   "  case lists:keyfind(<<\"xmlns\">>, 1, Attrs) of~n"
		   "    false ->~n"
		   "      encode(PNs, PNs, Name, Attrs, Children, J1, J2, J1L, J2L, Pfx);~n"
		   "    {_, Ns} ->~n"
		   "      encode(PNs, Ns, Name, Attrs, Children, J1, J2, J1L, J2L, Pfx)~n"
		   "  end;~n"
		   "encode_child({xmlcdata, Data}, _PNs, _J1, _J2, _J1L, _J2L, Pfx) ->~n"
		   "  <<Pfx/binary, 1:8, (encode_string(Data))/binary>>.~n~n", []),
    io:format(Dev, "encode_children(Children, PNs, J1, J2, J1L, J2L, Pfx) ->~n"
		   "  lists:foldl(~n"
		   "    fun(Child, Acc) ->~n"
		   "      encode_child(Child, PNs, J1, J2, J1L, J2L, Acc)~n"
		   "    end, Pfx, Children).~n~n", []),
    io:format(Dev, "encode_string(Data) ->~n"
		   "  <<V1:4, V2:6, V3:6>> = <<(byte_size(Data)):16/unsigned-big-integer>>,~n"
		   "  case {V1, V2, V3} of~n"
		   "    {0, 0, V3} ->~n"
		   "      <<V3:8, Data/binary>>;~n"
		   "    {0, V2, V3} ->~n"
		   "      <<(V3 bor 64):8, V2:8, Data/binary>>;~n"
		   "    _ ->~n"
		   "      <<(V3 bor 64):8, (V2 bor 64):8, V1:8, Data/binary>>~n"
		   "  end.~n~n", []),
    lists:foreach(
	fun({Ns, Els}) ->
	    io:format(Dev, "encode(PNs, ~p = Ns, Name, Attrs, Children, J1, J2, J1L, J2L, Pfx) ->~n"
			   "  case Name of~n", [Ns]),
	    lists:foreach(
		fun({ElN, Id, Attrs, Text}) ->
		    io:format(Dev, "    ~p ->~n", [ElN]),
		    case Attrs of
			[] ->
			    io:format(Dev, "      E = encode_attrs(Attrs, <<Pfx/binary, ~s>>),~n", [Id]);
			_ ->
			    io:format(Dev, "      E = lists:foldl(fun~n", []),
			    lists:foreach(
				fun({AName, AVals}) ->
				    case AVals of
					[AIdS] when is_binary(AIdS) ->
					    io:format(Dev, "        ({~p, AVal}, Acc) ->~n"
							   "          <<Acc/binary, ~s, (encode_string(AVal))/binary>>;~n",
						      [AName, AIdS]);
					_ ->
					    io:format(Dev, "        ({~p, AVal}, Acc) ->~n"
							   "          case AVal of~n", [AName]),
					    lists:foreach(
						fun({j1, AId}) ->
						    io:format(Dev, "            J1 -> <<Acc/binary, ~s>>;~n",
							      [AId]);
						   ({j2, AId}) ->
						       io:format(Dev, "            J2 -> <<Acc/binary, ~s>>;~n",
								 [AId]);
						   ({{j1}, AId}) ->
						       io:format(Dev, "            <<J1:J1L/binary, Rest/binary>> -> "
								      "<<Acc/binary, ~s, (encode_string(Rest))/binary>>;~n",
								 [AId]);
						   ({{j2}, AId}) ->
						       io:format(Dev, "            <<J2:J2L/binary, Rest/binary>> -> "
								      "<<Acc/binary, ~s, (encode_string(Rest))/binary>>;~n",
								 [AId]);
						   ({AVal, AId}) ->
						       io:format(Dev, "            ~p -> <<Acc/binary, ~s>>;~n",
								 [AVal, AId]);
						   (AId) ->
						       io:format(Dev, "            _ -> <<Acc/binary, ~s, "
								      "(encode_string(AVal))/binary>>~n",
								 [AId])
						end, AVals),
					    io:format(Dev, "          end;~n", [])
				    end
				end, Attrs),
			    io:format(Dev, "    (Attr, Acc) -> encode_attr(Attr, Acc)~n", []),
			    io:format(Dev, "  end, <<Pfx/binary, ~s>>, Attrs),~n", [Id])
		    end,
		    case Text of
			[] ->
			    io:format(Dev, "  E2 = encode_children(Children, Ns, "
					   "J1, J2, J1L, J2L, <<E/binary, 2:8>>),~n", []);
			_ ->
			    io:format(Dev, "  E2 = lists:foldl(fun~n", []),
			    lists:foreach(
				fun({TextV, TId}) ->
				    io:format(Dev, "    ({xmlcdata, ~p}, Acc) -> <<Acc/binary, ~s>>;~n", [TextV, TId])
				end, Text),
			    io:format(Dev, "    (El, Acc) -> encode_child(El, Ns, J1, J2, J1L, J2L, Acc)~n", []),
			    io:format(Dev, "  end, <<E/binary, 2:8>>, Children),~n", [])
		    end,
		    io:format(Dev, "  <<E2/binary, 4:8>>;~n", [])
		end, Els),
	    io:format(Dev, "  _ -> encode_el(PNs, Ns, Name, Attrs, Children, "
			   "J1, J2, J1L, J2L, Pfx)~nend;~n", [])
	end, Data),
    io:format(Dev, "encode(PNs, Ns, Name, Attrs, Children, J1, J2, J1L, J2L, Pfx) ->~n"
		   "  encode_el(PNs, Ns, Name, Attrs, Children, "
		   "J1, J2, J1L, J2L, Pfx).~n~n", []).

process_stats({_Counts, Stats}) ->
    SStats = lists:sort(
	fun({_, #el_stats{count = C1}}, {_, #el_stats{count = C2}}) ->
	    C1 >= C2
	end, maps:to_list(Stats)),
    lists:map(
	fun({Name, #el_stats{count = C, attrs = A, text_stats = T}}) ->
	    [Ns, El] = binary:split(Name, <<"<">>),
	    Attrs = lists:filtermap(
		fun({AN, #attr_stats{count = AC, vals = AV}}) ->
		    if
			AC*5 < C ->
			    false;
			true ->
			    AVC = AC div min(maps:size(AV)*2, 10),
			    AVA = [N || {N, C2} <- maps:to_list(AV), C2 > AVC],
			    {true, {AN, AVA}}
		    end
		end, maps:to_list(A)),
	    Text = [TE || {TE, TC} <- maps:to_list(T), TC > C/2],
	    {Ns, El, Attrs, Text}
	end, SStats).

analyze_elements(Elements, Stats, PName, PNS, J1, J2) ->
    lists:foldl(fun analyze_element/2, Stats, lists:map(fun(V) -> {V, PName, PNS, J1, J2} end, Elements)).

maps_update(Key, F, InitVal, Map) ->
    case maps:is_key(Key, Map) of
	true ->
	    maps:update_with(Key, F, Map);
	_ ->
	    maps:put(Key, F(InitVal), Map)
    end.

analyze_element({{xmlcdata, Data}, PName, PNS, _J1, _J2}, {ElCount, Stats}) ->
    Stats2 = maps_update(<<PNS/binary, "<", PName/binary>>,
	fun(#el_stats{text_stats = TS} = E) ->
	    TS2 = maps_update(Data, fun(C) -> C + 1 end, 0, TS),
	    E#el_stats{text_stats = TS2}
	end, #el_stats{}, Stats),
    {ElCount, Stats2};
analyze_element({#xmlel{name = Name, attrs = Attrs, children = Children}, _PName, PNS, J1, J2}, {ElCount, Stats}) ->
    XMLNS = case lists:keyfind(<<"xmlns">>, 1, Attrs) of
		{_, NS} ->
		    NS;
		false ->
		    PNS
	    end,
    NStats = maps_update(<<XMLNS/binary, "<", Name/binary>>,
	fun(#el_stats{count = C, empty_count = EC, only_text_count = TC, attrs = A} = ES) ->
	    A2 = lists:foldl(
		fun({<<"xmlns">>, _}, AMap) ->
		    AMap;
		   ({AName, AVal}, AMap) ->
		       J1S = size(J1),
		       J2S = size(J2),
		       AVal2 = case AVal of
				   J1 ->
				       j1;
				   J2 ->
				       j2;
				   <<J1:J1S/binary, _Rest/binary>> ->
				       {j1};
				   <<J2:J2S/binary, _Rest/binary>> ->
				       {j2};
				   Other ->
				       Other
			       end,
		       maps_update(AName, fun(#attr_stats{count = AC, vals = AV}) ->
			   AV2 = maps_update(AVal2, fun(C2) -> C2 + 1 end, 0, AV),
			   #attr_stats{count = AC + 1, vals = AV2}
					  end, #attr_stats{}, AMap)
		end, A, Attrs),
	    ES#el_stats{count = C + 1,
			empty_count = if Children == [] -> EC + 1; true ->
			    EC end,
			only_text_count = case Children of [{xmlcdata, _}] -> TC + 1; _ -> TC end,
			attrs = A2}
	end, #el_stats{}, Stats),
    analyze_elements(Children, {ElCount + 1, NStats}, Name, XMLNS, J1, J2).