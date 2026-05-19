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
          "CommentReport",
          "SpeedReport",
          "TestScore"
      }

CommentReport = symbol CommentReport
SpeedReport = symbol SpeedReport
TestScore = symbol TestScore

testAudit = method(Options => {CommentReport => false, SpeedReport => false, TestScore => false})

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

-- Only comment lines count for FIXME/TODO markers; otherwise this package
-- reports its own implementation strings as TODOs.
commentLineMatches := (pkg, pat) -> (
    filename := try pkg#"source file" else "";
    if filename === "" or not fileExists filename then {}
    else (
        srcLines := sourceLinesBeforeEnd filename;
        apply(select(lineNumbers(#srcLines), i -> match("^ *--", srcLines#i) and match(pat, srcLines#i)), i ->
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
-- TestScore report
--------------------------------------------------------------------------------

-- Empty categories count as satisfied rather than penalizing small packages.
scoreFraction := (covered, total) -> if total === 0 then 1 else covered / total

-- Compute a deliberately simple heuristic score.  It is meant to guide human
-- review, not certify test quality.
scoreReportLines := (inputs, syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos) -> (
    testedExports := #syms - #untestedExports;
    testedFunctions := #funcs - #untestedFunctions;
    testedTypes := #types - #(select(apply(types, toString), name -> member(name, untestedExports)));
    testedOthers := #others - #(select(apply(others, toString), name -> member(name, untestedExports)));
    testedOptions := #optionPairs - #untestedOptions;
    testedTotal := #syms + #optionPairs;
    testedCovered := testedExports + testedOptions;
    testedScore := 80 * scoreFraction(testedCovered, testedTotal);
    silencedScore := if #silencedTests === 0 then 10 else 0;
    todoScore := if #fixmeTodos >= 10 then 0 else 10 - #fixmeTodos;
    percentScore := toRR(testedScore + silencedScore + todoScore);

    {"", "TestScore: " | toString percentScore | " out of 100",
     "    tested: " | toString(toRR testedScore) | " out of 80",
     "    exports covered: " | toString(toRR(100 * scoreFraction(testedExports, #syms))) | "% (" | toString(testedExports) | "/" | toString(#syms) | ")",
     "    functions covered: " | toString(toRR(100 * scoreFraction(testedFunctions, #funcs))) | "% (" | toString(testedFunctions) | "/" | toString(#funcs) | ")",
     "    types covered: " | toString(toRR(100 * scoreFraction(testedTypes, #types))) | "% (" | toString(testedTypes) | "/" | toString(#types) | ")",
     "    other exports covered: " | toString(toRR(100 * scoreFraction(testedOthers, #others))) | "% (" | toString(testedOthers) | "/" | toString(#others) | ")",
     "    options covered: " | toString(toRR(100 * scoreFraction(testedOptions, #optionPairs))) | "% (" | toString(testedOptions) | "/" | toString(#optionPairs) | ")",
     "    no silenced tests: " | toString(silencedScore) | " out of 10",
     "    FIXME/TODO markers: " | toString(todoScore) | " out of 10 (" | toString(#fixmeTodos) | " found)"}
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
    fixmeTodos := commentLineMatches(pkg, "FIXME|TODO|fixme|todo");

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
        (if opts.TestScore then scoreReportLines(inputs, syms, funcs, types, others, untestedExports, untestedFunctions, optionPairs, untestedOptions, silencedTests, fixmeTodos) else {}) |
        (if opts.SpeedReport then speedReportLines(pkg, inputs) else {}) |
        (if opts.CommentReport then commentReportLines inputs else {});

    report := demark(newline, reportLines);
    report
)

-- Load documentation so package TEST blocks are available.
testAudit String := opts -> pkgname -> testAudit(needsPackage(pkgname, LoadDocumentation => true), opts)



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
      Headline
        produce a test audit report for a package
      Usage
        testAudit pkg
      Inputs
        pkg:{Package,String}
      Outputs
        :String
          the audit report
      Description
        Text
          This function returns a report about the tests of @TT "pkg"@.
          The report includes the number of tests, the source files containing tests, a style classification, exported functions and options not mentioned in tests, silenced tests, and FIXME or TODO comments.
        Text
          The style line may include @TT "no tests"@, @TT "auxiliary"@, @TT "interspersed"@, or @TT "together"@.
        Text
          Optional sections can be included using the following Boolean options.
        Tree
          :Optional report sections
            [testAudit, CommentReport]
            [testAudit, SpeedReport]
            [testAudit, TestScore]
        Example
          testAudit "TestAudit"
      SeeAlso
        CommentReport
        SpeedReport
        TestScore
      ///

      doc ///
      Key
        CommentReport
        [testAudit, CommentReport]
      Headline
        include comments from tests in the audit report
      Usage
        testAudit(..., CommentReport => Boolean)
      Description
        Text
          If @TT "CommentReport => true"@, then the report includes comments attached to or appearing inside tests.
          Tests with no comments are omitted from this section.
      ///

      doc ///
      Key
        SpeedReport
        [testAudit, SpeedReport]
      Headline
        include timing information for tests
      Usage
        testAudit(..., SpeedReport => Boolean)
      Description
        Text
          If @TT "SpeedReport => true"@, then each test is run with @TO check@ and the report includes elapsed timing information.
      ///

      doc ///
      Key
        TestScore
        [testAudit, TestScore]
      Headline
        include a heuristic score in the audit report
      Usage
        testAudit(..., TestScore => Boolean)
      Description
        Text
          If @TT "TestScore => true"@, then the report includes a heuristic score out of 100.
        Text
          Test Coverage: 80 points. 
        Text
          No Silenced Tests: 10 points.
        Text
          No FIXME/TODO: 10 points.
      ///

      --testAudit test
      TEST /// 
        pkg = loadPackage("Complexes", Reload=>true);
        testAudit(pkg)
      ///
      
      --CommentReport option test
      TEST /// 
        pkg = loadPackage("Complexes", Reload=>true);
        testAudit(pkg, CommentReport=>true)
      ///

      --SpeedReport option test
      TEST /// 
        pkg = loadPackage("Depth", Reload=>true);
        testAudit(pkg, SpeedReport=>true)
      ///

      --TestScore option test
      TEST ///
        pkg = loadPackage("Depth", Reload=>true);
        report = testAudit(pkg, TestScore=>true);
        assert match("TestScore: .* out of 100", report)
      ///

      end--

      -* Development section *-
      restart
      debug needsPackage "TestAudit"
      check "TestAudit"

      uninstallPackage "TestAudit"
      restart
      installPackage "TestAudit"
      viewHelp "TestAudit"
