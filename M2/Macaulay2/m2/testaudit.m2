CommentReport = symbol CommentReport

testAudit = method(Options => {CommentReport => false})

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

testInputs = method()

testInputs Package := pkg -> tests pkg

testInputs String := pkgname -> testInputs needsPackage(pkgname, LoadDocumentation => true)


testCodeString = method()

testCodeStringFromInputs := inputs -> (
    demark(newline, apply(toList(0..#inputs-1), i -> inputs#i#"code"))
)

testCodeString Package := pkg -> testCodeStringFromInputs testInputs pkg

testCodeString String := pkgname -> testCodeString needsPackage(pkgname, LoadDocumentation => true)


packageSourceString = method()

packageSourceString Package := pkg -> try get pkg#"source file" else ""

packageSourceString String := pkgname -> packageSourceString needsPackage(pkgname, LoadDocumentation => true)


exportedSymbols = method()

exportedSymbols Package := pkg -> sort toList pkg#"exported symbols"

exportedSymbols String := pkgname -> exportedSymbols needsPackage(pkgname, LoadDocumentation => true)


exportedValue := s -> try value s else null

className := x -> toString class x

isExportedFunction := s -> (
    v := exportedValue s;
    member(className v, {"MethodFunction", "MethodFunctionWithOptions", "FunctionClosure", "Function"})
)

isExportedType := s -> (
    v := exportedValue s;
    className v === "Type"
)

optionNamesForSymbol := s -> (
    v := exportedValue s;
    try sort apply(toList keys options v, toString) else {}
)

methodStringsForSymbol := s -> (
    v := exportedValue s;
    try sort apply(toList methods v, toString) else {}
)

wordMatch := (name, code) -> match("\\b" | toString name | "\\b", code)

countLinesMatching := (pat, code) -> #select(lines code, line -> match(pat, line))

shortList := (L, n) -> (
    if #L === 0 then ""
    else if #L <= n then demark(", ", L)
    else demark(", ", take(L, n)) | ", ..."
)

lineNumbers := n -> if n === 0 then {} else toList(0..n-1)

snippet := (s, n) -> (
    t := replace("^ *| *$", "", s);
    if length t <= n then t else substring(0, n, t) | "..."
)

auditListLines := (label, L) -> (
    {"- " | label | " (" | toString(#L) | "):"} |
    (if #L === 0 then {"    none"} else apply(L, item -> "    - " | item)) |
    {""}
)

printAuditList := (label, L) -> (
    scan(auditListLines(label, L), print);
)

sourceLinesBeforeEnd := filename -> (
    srcLines := lines get filename;
    endLines := select(lineNumbers(#srcLines), i -> match("^ *end *$", srcLines#i));
    if #endLines === 0 then srcLines else take(srcLines, first endLines)
)

sourceLineMatches := (pkg, pat) -> (
    filename := try pkg#"source file" else "";
    if filename === "" or not fileExists filename then {}
    else (
        srcLines := sourceLinesBeforeEnd filename;
        apply(select(lineNumbers(#srcLines), i -> match(pat, srcLines#i)), i ->
            snippet(srcLines#i, 72) | " (source: " | filename | ":" | toString(i + 1) | ")")
    )
)

blockCommentLineMatches := (pkg, pat) -> (
    filename := try pkg#"source file" else "";
    if filename === "" or not fileExists filename then {}
    else (
        srcLines := sourceLinesBeforeEnd filename;
        inBlock := false;
        matches := {};
        scan(lineNumbers(#srcLines), i -> (
            line := srcLines#i;
            startsBlock := match("-\\*", line);
            endsBlock := match("\\*-", line);
            wasInBlock := inBlock;

            if startsBlock then inBlock = true;
            if (wasInBlock or startsBlock) and match(pat, line) then (
                matches = append(matches, snippet(line, 72) | " (source: " | filename | ":" | toString(i + 1) | ")")
            );
            if endsBlock then inBlock = false;
        ));
        matches
    )
)

silencedTestMatches := pkg -> unique(sourceLineMatches(pkg, "^ *--+ *TEST *///") | blockCommentLineMatches(pkg, "TEST *///"))

styleOfTests := inputs -> (
    locs := apply(toList(0..#inputs-1), i -> toString locate inputs#i);
    if any(locs, loc -> match("/tests/", loc)) then "auxiliary file(s)"
    else "interspersed"
)

containsAll := (code, names) -> all(names, name -> wordMatch(name, code))

typeNamesInMethodString := meth -> (
    parts := separate(",", replace("^\\([^,]*,?|\\)$", "", meth));
    select(apply(parts, s -> replace("^ *| *$", "", s)), s -> s =!= "")
)

isMethodTested := (meth, code) -> (
    pieces := separate(",", replace("^\\(|\\)$", "", meth));
    if #pieces === 0 then false
    else (
        functionName := replace("^ *| *$", "", first pieces);
        wordMatch(functionName, code) and containsAll(code, typeNamesInMethodString meth)
    )
)

--------------------------------------------------------------------------------
-- Comment report
--------------------------------------------------------------------------------

commentLinesIn := code -> select(lines code, line -> match("^ *--", line) and not match("^ *-- test source:", line))

commentReportLines := inputs -> (
    {"", "Comments:"} | flatten apply(toList(0..#inputs-1), i -> (
        code := inputs#i#"code";
        comments := commentLinesIn code;

        if #comments > 0
        then {"", "TEST " | toString i | " -- source: " | toString locate inputs#i, "-----------------------------"} | comments
        else {}
    ))
)

printCommentReport := inputs -> (
    scan(commentReportLines inputs, print);
)

--------------------------------------------------------------------------------
-- Main audit
--------------------------------------------------------------------------------

testAudit Package := opts -> pkg -> (
    inputs := testInputs pkg;
    code := testCodeStringFromInputs inputs;
    sourceCode := packageSourceString pkg;
    syms := exportedSymbols pkg;

    funcs := select(syms, isExportedFunction);
    types := select(syms, isExportedType);
    others := select(syms, s -> not isExportedFunction s and not isExportedType s);

    untestedFunctions := select(apply(funcs, toString), name -> not wordMatch(name, code));

    optionPairs := flatten apply(funcs, f -> apply(optionNamesForSymbol f, opt -> {toString f, opt}));
    untestedOptions := select(optionPairs, pair -> (
        opt := pair#1;
        not wordMatch(opt, code)
    ));
    untestedOptionLabels := apply(untestedOptions, pair -> pair#0 | ": " | pair#1);

    methodPairs := flatten apply(funcs, f -> methodStringsForSymbol f);
    untestedMethods := select(methodPairs, meth -> not isMethodTested(meth, code));

    silencedTests := silencedTestMatches pkg;
    fixmeTodos := sourceLineMatches(pkg, "FIXME|TODO|fixme|todo");

    reportLines := {
        "exported: " | toString(#funcs) | " functions, " | toString(#types) | " types, " | toString(#others) | " other symbols",
        "n_tests: " | toString(#inputs),
        "style: " | styleOfTests inputs,
        "",
        "Report:",
        ""
        } |
        auditListLines("untested functions", untestedFunctions) |
        auditListLines("untested options", untestedOptionLabels) |
        auditListLines("untested methods", untestedMethods) |
        auditListLines("silenced tests", silencedTests) |
        auditListLines("FIXME/TODO markers", fixmeTodos) |
        (if opts.CommentReport then commentReportLines inputs else {});

    report := demark(newline, reportLines);
    print report;
    report
)

testAudit String := opts -> pkgname -> testAudit(needsPackage(pkgname, LoadDocumentation => true), opts)
