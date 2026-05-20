newPackage(
          "TestAudit",
          Version => "0.1",
          Date => "May 19, 2026",
          Headline => "Provides test audit functionality",
          Authors => {{ Name => "Taylor Brysiewicz", Email => "tbrysiew@uwo.ca", HomePage => "https://sites.google.com/view/taylorbrysiewicz/home"}},
          Keywords => {"Miscellaneous"},
          AuxiliaryFiles => false,
          DebuggingMode => false
          )

      export {
          "testAudit",
          "testScore",
          "CommentReport",
          "SpeedReport",
          "ScoreReport"
      }

CommentReport = symbol CommentReport
SpeedReport = symbol SpeedReport
ScoreReport = symbol ScoreReport

testAudit = method(Options => {CommentReport => false, SpeedReport => false, ScoreReport => false})
testScore = method()

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

testInputs = method()
testInputs Package := pkg -> tests pkg
testInputs String := pkgname -> testInputs needsPackage(pkgname, LoadDocumentation => true)


-- The coverage checks below are textual heuristics, not dispatch tracing.
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


-- These helpers classify exported symbols by the class of their current value.
-- Anything not recognized as function-like or a Type is reported as "other".
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

wordMatch := (name, code) -> match("\\b" | toString name | "\\b", code)

countLinesMatching := (pat, code) -> #select(lines code, line -> match(pat, line))

shortList := (L, n) -> (
    if #L === 0 then ""
    else if #L <= n then demark(", ", L)
    else demark(", ", take(L, n)) | ", ..."
)

-- Avoid constructing the invalid range 0..-1 when a list is empty.
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

-- Ignore development scratch code after a literal "end" line in package files.
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

actualCodeLine := line -> not match("^\\s*$", line) and not match("^\\s*--", line)

actualCodeBetweenTests := (filename, firstLoc, secondLoc) -> (
    if not fileExists filename then false
    else (
        srcLines := lines get filename;
        firstLine := firstLoc#3 + 1;
        lastLine := secondLoc#1 - 1;
        codeLines := if firstLine <= lastLine then select(toList(firstLine..lastLine), n ->
            n >= 1 and n <= #srcLines and actualCodeLine srcLines#(n - 1)) else {};
        #codeLines > 0
    )
)

-- Sort FilePositions indirectly; FilePosition itself has no useful ordering.
interspersedTests := locs -> (
    files := unique apply(locs, loc -> loc#0);
    any(files, filename -> (
        fileLocs := last \ sort apply(select(toList(0..#locs-1), i -> (locs#i)#0 === filename),
            i -> ((locs#i)#1, i, locs#i));
        #fileLocs > 1 and any(toList(0..#fileLocs-2), i ->
            actualCodeBetweenTests(filename, fileLocs#i, fileLocs#(i + 1)))
    ))
)

-- "auxiliary" means tests come from more than one file; "together" means tests
-- exist and are not interspersed with code.
styleOfTests := inputs -> (
    if #inputs === 0 then {"no tests"}
    else (
        locs := apply(toList(0..#inputs-1), i -> locate inputs#i);
        styles := {};
        interspersed := interspersedTests locs;
        if #(unique apply(locs, loc -> loc#0)) > 1 then styles = append(styles, "auxiliary");
        styles = append(styles, if interspersed then "interspersed" else "together");
        styles
    )
)

testSourceLines := inputs -> (
    locs := apply(lineNumbers(#inputs), i -> locate inputs#i);
    files := unique apply(locs, loc -> loc#0);
    {"test sources:"} |
    (if #files === 0
     then {"    none"}
     else apply(files, file -> (
         firstLine := first sort apply(select(locs, loc -> loc#0 === file), loc -> loc#1);
         "    - " | file | ":" | toString firstLine
     )))
)

--------------------------------------------------------------------------------
-- Comment report
--------------------------------------------------------------------------------

-- Exclude the synthetic "-- test source:" line Macaulay2 adds to TestInput code.
commentLinesIn := code -> select(lines code, line -> match("^ *--", line) and not match("^ *-- test source:", line))

-- Look immediately above a TEST block for a contiguous run of -- comments.
headerCommentLinesBefore := testInput -> (
    loc := locate testInput;
    filename := loc#0;
    startLine := loc#1;
    if not fileExists filename then {}
    else (
        srcLines := lines get filename;
        i := startLine - 2;
        comments := {};
        while i >= 0 and match("^ *--", srcLines#i) do (
            comments = prepend(srcLines#i, comments);
            i = i - 1;
        );
        comments
    )
)

testCommentLineIndices := testInput -> (
    loc := locate testInput;
    filename := loc#0;
    startLine := loc#1;
    endLine := loc#3;
    if not fileExists filename then {filename, {}}
    else (
        srcLines := lines get filename;
        headerIndices := {};
        i := startLine - 2;
        while i >= 0 and match("^ *--", srcLines#i) do (
            headerIndices = prepend(i, headerIndices);
            i = i - 1;
        );
        testIndices := if startLine <= endLine then select(toList(startLine-1..endLine-1), j ->
            j >= 0 and j < #srcLines and match("^ *--", srcLines#j)) else {};
        {filename, unique(headerIndices | testIndices)}
    )
)

taskMarkerMatches := inputs -> (
    pat := "^ *--+ *([Ff][Ii][Xx][Mm][Ee]|[Tt][Oo][Dd][Oo])\\b";
    unique flatten apply(lineNumbers(#inputs), i -> (
        indexedLines := testCommentLineIndices inputs#i;
        filename := indexedLines#0;
        if filename === "" or not fileExists filename then {}
        else (
            srcLines := lines get filename;
            apply(select(indexedLines#1, j -> match(pat, srcLines#j)), j ->
                snippet(srcLines#j, 72) | " (source: " | filename | ":" | toString(j + 1) | ")")
        )
    ))
)

commentSectionLines := (label, comments) -> (
    {label | ":"} | apply(comments, c -> "    " | c)
)

-- Tests with no comments are skipped; a package with none gets "(no comments)".
commentReportLines := inputs -> (
    blocks := flatten apply(toList(0..#inputs-1), i -> (
        code := inputs#i#"code";
        headerComments := headerCommentLinesBefore inputs#i;
        inTestComments := commentLinesIn code;

        if #headerComments > 0 or #inTestComments > 0
        then {"", "TEST " | toString i | " -- source: " | toString locate inputs#i, "------------------------------------------------------------------------"} |
            commentSectionLines("Header comments", headerComments) |
            commentSectionLines("In-test comments", inTestComments)
        else {}
    ));
    {"", "Comments:"} | if #blocks === 0 then {"(no comments)"} else blocks
)

printCommentReport := inputs -> (
    scan(commentReportLines inputs, print);
)

--------------------------------------------------------------------------------
-- Speed report
--------------------------------------------------------------------------------

timeString := seconds -> toString seconds | "s"

-- Timing failures are reported per test rather than aborting the audit.
speedReportLines := (pkg, inputs) -> (
    timings := apply(toList(0..#inputs-1), i -> (
        result := try (
            t := elapsedTiming check(i, pkg);
            {i, t#0, toString locate inputs#i, true}
        ) else {i, null, toString locate inputs#i, false};
        result
    ));
    successful := select(timings, row -> row#3);
    totalTime := sum apply(successful, row -> row#1);

    {"", "Speed Report:", ""} |
    apply(timings, row -> (
        if row#3
        then "    - TEST " | toString(row#0) | ": " | timeString(row#1) | " (" | row#2 | ")"
        else "    - TEST " | toString(row#0) | ": failed while timing (" | row#2 | ")"
    )) |
    {"", "    total timed tests: " | toString(#successful) | "/" | toString(#timings),
     "    total time: " | timeString totalTime}
)

--------------------------------------------------------------------------------
-- ScoreReport report
--------------------------------------------------------------------------------

-- Empty categories count as satisfied rather than penalizing small packages.
scoreFraction := (covered, total) -> if total === 0 then 1 else covered / total

scoreValues := (syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos) -> (
    testedExports := #syms - #untestedExports;
    testedFunctions := #funcs - #untestedFunctions;
    testedTypes := #types - #(select(apply(types, toString), name -> member(name, untestedExports)));
    testedOthers := #others - #(select(apply(others, toString), name -> member(name, untestedExports)));
    testedOptions := #optionPairs - #untestedOptions;
    testedTotal := #syms + #optionPairs;
    testedCovered := testedExports + testedOptions;
    testedScore := toRR(80 * scoreFraction(testedCovered, testedTotal));
    silencedScore := max(0, 10 - #silencedTests);
    todoScore := max(0, 10 - #fixmeTodos);
    totalScore := toRR(testedScore + silencedScore + todoScore);
    scoreLines := {
        "ScoreReport: " | toString totalScore | " out of 100",
        "    tested: " | toString(testedScore) | " out of 80",
        "    exports covered: " | toString(toRR(100 * scoreFraction(testedExports, #syms))) | "% (" | toString(testedExports) | "/" | toString(#syms) | ")",
        "    functions covered: " | toString(toRR(100 * scoreFraction(testedFunctions, #funcs))) | "% (" | toString(testedFunctions) | "/" | toString(#funcs) | ")",
        "    types covered: " | toString(toRR(100 * scoreFraction(testedTypes, #types))) | "% (" | toString(testedTypes) | "/" | toString(#types) | ")",
        "    other exports covered: " | toString(toRR(100 * scoreFraction(testedOthers, #others))) | "% (" | toString(testedOthers) | "/" | toString(#others) | ")",
        "    options covered: " | toString(toRR(100 * scoreFraction(testedOptions, #optionPairs))) | "% (" | toString(testedOptions) | "/" | toString(#optionPairs) | ")",
        "    silenced tests: " | toString(silencedScore) | " out of 10 (" | toString(#silencedTests) | " found)",
        "    FIXME/TODO markers: " | toString(todoScore) | " out of 10 (" | toString(#fixmeTodos) | " found)"};
    {totalScore, scoreLines}
)

-- Compute a deliberately simple heuristic score.  It is meant to guide human
-- review, not certify test quality.
scoreReportLines := (inputs, syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos) -> (
    {""} | (scoreValues(syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos))#1
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

    untestedExports := select(apply(syms, toString), name -> not wordMatch(name, code));
    untestedFunctions := select(apply(funcs, toString), name -> member(name, untestedExports));

    optionPairs := flatten apply(funcs, f -> apply(optionNamesForSymbol f, opt -> {toString f, opt}));
    untestedOptions := select(optionPairs, pair -> (
        opt := pair#1;
        not wordMatch(opt, code)
    ));
    untestedOptionLabels := apply(untestedOptions, pair -> pair#0 | ": " | pair#1);

    silencedTests := silencedTestMatches pkg;
    fixmeTodos := taskMarkerMatches inputs;

    reportLines := {
        "exported: " | toString(#funcs) | " functions, " | toString(#types) | " types, " | toString(#others) | " other symbols",
        "n_tests: " | toString(#inputs),
        "style: " | demark(", ", styleOfTests inputs),
        ""} |
        testSourceLines inputs |
        {"",
        "Report:",
        ""
        } |
        auditListLines("untested functions", untestedFunctions) |
        auditListLines("untested options", untestedOptionLabels) |
        auditListLines("silenced tests", silencedTests) |
        auditListLines("FIXME/TODO markers", fixmeTodos) |
        (if opts.ScoreReport then scoreReportLines(inputs, syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos) else {}) |
        (if opts.SpeedReport then speedReportLines(pkg, inputs) else {}) |
        (if opts.CommentReport then commentReportLines inputs else {});

    report := demark(newline, reportLines);
    report
)

-- Load documentation so package TEST blocks are available.
testAudit String := opts -> pkgname -> testAudit(needsPackage(pkgname, LoadDocumentation => true), opts)

testScore Package := pkg -> (
    inputs := testInputs pkg;
    code := testCodeStringFromInputs inputs;
    syms := exportedSymbols pkg;
    funcs := select(syms, isExportedFunction);
    types := select(syms, isExportedType);
    others := select(syms, s -> not isExportedFunction s and not isExportedType s);

    untestedExports := select(apply(syms, toString), name -> not wordMatch(name, code));
    untestedFunctions := select(apply(funcs, toString), name -> member(name, untestedExports));
    optionPairs := flatten apply(funcs, f -> apply(optionNamesForSymbol f, opt -> {toString f, opt}));
    untestedOptions := select(optionPairs, pair -> not wordMatch(pair#1, code));

    silencedTests := silencedTestMatches pkg;
    fixmeTodos := taskMarkerMatches inputs;

    (scoreValues(syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos))#0
)

-- Load documentation so package TEST blocks are available.
testScore String := pkgname -> testScore needsPackage(pkgname, LoadDocumentation => true)



      -* Documentation section *-
      beginDocumentation()
      doc ///
      Key
        TestAudit
      Headline
        Provides test audit functionality
      Description
        Text
          The @TT "TestAudit"@ package provides a small report about the tests of a package.
          The report lists the number and location of tests, classifies how tests are organized, and gives simple textual checks for exported functions, options, silenced tests, and FIXME or TODO comments.
      ///
      doc ///
      Key
        testAudit
        (testAudit, Package)
        (testAudit, String)
        CommentReport
        [testAudit, CommentReport]
        SpeedReport
        [testAudit, SpeedReport]
        ScoreReport
        [testAudit, ScoreReport]
      Headline
        produce a test audit report for a package
      Usage
        testAudit pkg
        testAudit(pkg, CommentReport => true, SpeedReport => true, ScoreReport => true)
      Inputs
        pkg:{Package,String}
        CommentReport => Boolean
        SpeedReport => Boolean
        ScoreReport => Boolean
      Outputs
        :String
          the audit report
      Description
        Text
          Returns a string report about the tests of @TT "pkg"@.
          The default report summarizes test sources, test organization, untested exported functions and options, silenced tests, and FIXME or TODO markers around test blocks.
        Text
          Optional Boolean arguments add sections: @TT "CommentReport"@ includes comments attached to tests, @TT "SpeedReport"@ times tests with @TO check@, and @TT "ScoreReport"@ includes the heuristic score returned by @TO testScore@.
        Example
          testAudit "TestAudit"
      SeeAlso
        testAudit
      ///

      doc ///
      Key
        testScore
        (testScore, Package)
        (testScore, String)
      Headline
        compute the heuristic test score for a package
      Usage
        testScore pkg
      Inputs
        pkg:{Package,String}
      Outputs
        :RR
          the heuristic test score
      Description
        Text
          This function returns only the numerical score that appears in the @TT "ScoreReport"@ section of @TO testAudit@.
          The score is out of 100.
        Example
          testScore "TestAudit"
      SeeAlso
        testAudit
      ///

--testAudit test
TEST /// 
  testAudit("TestAudit")
///

--CommentReport option test
TEST /// 
  testAudit("TestAudit", CommentReport=>true)
///

--SpeedReport option test (cannot call on TestAudit because)
--infinite recursion...
TEST /// 
  testAudit("ConwayPolynomials", SpeedReport=>true)
///

--ScoreReport option test
TEST ///
  report = testAudit("TestAudit", ScoreReport=>true);
///

--testScore test
TEST ///
  score = testScore "TestAudit";
  assert(score >= 0 and score <= 100)
///

end

restart
