Base.eval(quote
    function show_method_candidates(io::IO, ex::MethodError, kwargs::Vector=Any[])
    is_arg_types = isa(ex.args, DataType)
    arg_types = is_arg_types ? ex.args : typesof(ex.args...)
    arg_types_param = Any[arg_types.parameters...]
    # Displays the closest candidates of the given function by looping over the
    # functions methods and counting the number of matching arguments.
    f = ex.f
    ft = typeof(f)
    lines = []
    # These functions are special cased to only show if first argument is matched.
    special = f in [convert, getindex, setindex!]
    funcs = Any[(f, arg_types_param)]

    # An incorrect call method produces a MethodError for convert.
    # It also happens that users type convert when they mean call. So
    # pool MethodErrors for these two functions.
    if f === convert && !isempty(arg_types_param)
        at1 = arg_types_param[1]
        if isa(at1,DataType) && (at1::DataType).name === Type.body.name && isleaftype(at1)
            push!(funcs, (at1.parameters[1], arg_types_param[2:end]))
        end
    end

    const CANDIDATE_LIMIT = 3
    for (func,arg_types_param) in funcs
        for (i,method) in enumerate(methods(unwrap_unionall(func)))
            i > CANDIDATE_LIMIT && break
            buf = IOBuffer()
            tv = Any[]
            sig0 = method.sig
            if Base.is_default_method(method)
                continue
            end
            while isa(sig0, UnionAll)
                push!(tv, sig0.var)
                sig0 = sig0.body
            end
            sig0 = unwrap_unionall(sig0)
            s1 = sig0.parameters[1]
            sig = sig0.parameters[2:end]
            print(buf, "  ")
            if !isa(func, s1)
                # function itself doesn't match
                return
            else
                # TODO: use the methodshow logic here
                if isa(func, Type)
                    if isa(func, UnionAll)
                        print(buf, unwrap_unionall(func).name)
                    else
                        print(buf, func.name)
                    end
                else
                    print(buf, typeof(func).name.mt.name)
                end
            end
            print(buf, "(")
            t_i = copy(arg_types_param)
            right_matches = 0

            # We don't want TypeVars to display their bounds when they
            # are stringified as the types of arguments, since it is redundant with the `where` clause.
            function stringify(param)
                isa(param, TypeVar) && return param.name
                return string(param)
            end
            stringify(param, extra_strings::String...) = string(stringify(param), extra_strings...)

            for i = 1 : min(length(t_i), length(sig))
                i > 1 && print(buf, ", ")
                # If isvarargtype then it checks whether the rest of the input arguments matches
                # the varargtype
                if Base.isvarargtype(sig[i])
                    sigstr = stringify(unwrap_unionall(sig[i]).parameters[1], "...")
                    j = length(t_i)
                else
                    sigstr = stringify(sig[i])
                    j = i
                end
                # Checks if the type of arg 1:i of the input intersects with the current method
                t_in = typeintersect(rewrap_unionall(Tuple{sig[1:i]...}, method.sig),
                                     rewrap_unionall(Tuple{t_i[1:j]...}, method.sig))
                # If the function is one of the special cased then it should break the loop if
                # the type of the first argument is not matched.
                t_in === Union{} && special && i == 1 && break
                if t_in === Union{}
                    if Base.have_color
                        Base.with_output_color(Base.error_color(), buf) do buf
                            print(buf, "::$sigstr")
                        end
                    else
                        print(buf, "!Matched::$sigstr")
                    end
                    # If there is no typeintersect then the type signature from the method is
                    # inserted in t_i this ensures if the type at the next i matches the type
                    # signature then there will be a type intersect
                    t_i[i] = sig[i]
                else
                    right_matches += j==i ? 1 : 0
                    print(buf, "::$sigstr")
                end
            end
            special && right_matches==0 && return # continue the do-block

            if length(t_i) > length(sig) && !isempty(sig) && Base.isvarargtype(sig[end])
                # It ensures that methods like f(a::AbstractString...) gets the correct
                # number of right_matches
                for t in arg_types_param[length(sig):end]
                    if t <: rewrap_unionall(unwrap_unionall(sig[end]).parameters[1], method.sig)
                        right_matches += 1
                    end
                end
            end

            if right_matches > 0 || length(ex.args) < 2
                if length(t_i) < length(sig)
                    # If the methods args is longer than input then the method
                    # arguments is printed as not a match
                    for (k, sigtype) in enumerate(sig[length(t_i)+1:end])
                        sigtype = isvarargtype(sigtype) ? unwrap_unionall(sigtype) : sigtype
                        if Base.isvarargtype(sigtype)
                            sigstr = stringify(sigtype.parameters[1], "...")
                        else
                            sigstr = stringify(sig[i])
                        end
                        if !((min(length(t_i), length(sig)) == 0) && k==1)
                            print(buf, ", ")
                        end
                        if Base.have_color
                            Base.with_output_color(Base.error_color(), buf) do buf
                                print(buf, "::$sigstr")
                            end
                        else
                            print(buf, "!Matched::$sigstr")
                        end
                    end
                end
            end
            if right_matches > 0 || length(ex.args) < 2
                kwords = Symbol[]
                if isdefined(ft.name.mt, :kwsorter)
                    kwsorter_t = typeof(ft.name.mt.kwsorter)
                    kwords = kwarg_decl(method, kwsorter_t)
                    length(kwords) > 0 && print(buf, "; ", join(kwords, ", "))
                end
                print(buf, ")")
                show_method_params(buf, tv)
                print(buf, " at ", method.file, ":", method.line)
                if !isempty(kwargs)
                    unexpected = Symbol[]
                    if isempty(kwords) || !(any(endswith(string(kword), "...") for kword in kwords))
                        for (k, v) in kwargs
                            if !(k in kwords)
                                push!(unexpected, k)
                            end
                        end
                    end
                    if !isempty(unexpected)
                        Base.with_output_color(Base.error_color(), buf) do buf
                            plur = length(unexpected) > 1 ? "s" : ""
                            print(buf, " got unsupported keyword argument$plur \"", join(unexpected, "\", \""), "\"")
                        end
                    end
                end
                if ex.world < min_world(method)
                    print(buf, " (method too new to be called from this world context.)")
                end
                if ex.world > max_world(method)
                    print(buf, " (method deleted before this world age.)")
                end
                # TODO: indicate if it's in the wrong world
                push!(lines, (buf, right_matches))
            end
        end
    end

    if !isempty(lines) # Display up to three closest candidates
        Base.with_output_color(:normal, io) do io
            println(io)
            print(io, "Closest candidates are:")
            sort!(lines, by = x -> -x[2])
            i = 0
            for line in lines
                println(io)
                if i > CANDIDATE_LIMIT
                    print(io, "  ...")
                    break
                end
                i += 1
                print(io, String(take!(line[1])))
            end
        end
    end
end)