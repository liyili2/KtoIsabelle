// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.Backends;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.FirstStep;
import org.kframework.backend.LastStep;
import org.kframework.backend.java.compile.AddLocalRewritesUnderCells;
import org.kframework.backend.java.compile.ComputeCellsOfInterest;
import org.kframework.backend.java.compile.DataStructureToLookupUpdate;
import org.kframework.backend.java.compile.GenerateKRewriteMachineInstructions;
import org.kframework.backend.java.compile.JavaBackendCell2DataStructure;
import org.kframework.backend.java.compile.KORECompilationSteps;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.DeclareCellLabels;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.*;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.CollectBracketsVisitor;
import org.kframework.kil.loader.CollectProductionsVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.GeneratedHeatingCoolingRules;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;
import com.google.inject.Provider;


/**
 * Backend for the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class JavaSymbolicBackend extends BasicBackend {

    public static final String DEFINITION_FILENAME = "java_symbolic_definition.bin";

    private final BinaryLoader loader;
    private final Provider<RuleIndex> index;
    private final Provider<KILtoBackendJavaKILTransformer> transformer;
    private final FileUtil files;
    private final KExceptionManager kem;

    @Inject
    JavaSymbolicBackend(
            Stopwatch sw,
            Context context,
            KompileOptions options,
            BinaryLoader loader,
            Provider<RuleIndex> index,
            Provider<KILtoBackendJavaKILTransformer> transformer,
            FileUtil files,
            KExceptionManager kem) {
        super(sw, context, options);
        this.loader = loader;
        this.index = index;
        this.transformer = transformer;
        this.files = files;
        this.kem = kem;
    }

    @Override
    public Definition lastStep(Definition javaDef) {
        org.kframework.backend.java.kil.Definition definition = transformer.get().transformDefinition(javaDef);

        definition.setIndex(index.get());

        loader.saveOrDie(files.resolveKompiled(JavaSymbolicBackend.DEFINITION_FILENAME),
                definition);

        return javaDef;
    }

    @Override
    public void run(Definition def) { }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        
        steps.add(new FirstStep(this, context));
        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        steps.add(new RemoveBrackets(context));
        // SetVariablesInferredSort must be performed before AddEmptyLists
        steps.add(new SetVariablesInferredSort(context));
        steps.add(new AddEmptyLists(context, kem));
        steps.add(new RemoveSyntacticCasts(context));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context, kem), context));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));

        steps.add(new KORECompilationSteps(context));

        steps.add(new FlattenModules(context, kem));

        //steps.add(new CompleteSortLatice(context));
        steps.add(new CheckVisitorStep<Definition>(new CollectProductionsVisitor(context), context));
        steps.add(new CheckVisitorStep<Definition>(new CollectSubsortsVisitor(context), context));
        steps.add(new CheckVisitorStep<Definition>(new CollectBracketsVisitor(context), context));
        steps.add(new AddInjections(context));

/*will need this in the future.
        steps.add(new GeneratedHeatingCoolingRules(context));
        
       // steps.add(new FreezeUserFreezers(context));
        //steps.add(new ContextsToHeating(context));
        //steps.add(new AddSupercoolDefinition(context));
        //steps.add(new AddHeatingConditions(context));
        //steps.add(new AddSuperheatRules(context));
        
        steps.add(new DesugarStreams(context));
        steps.add(new ResolveFunctions(context));
        steps.add(new AddKCell(context));
        
        steps.add(new AddStreamCells(context));
        steps.add(new ResolveHybrid(context));
        //steps.add(new AddSymbolicK(context));
        //steps.add(new AddSemanticEquality(context));
        // steps.add(new ResolveFresh());
        //steps.add(new FreshCondToFreshVar(context));
        //steps.add(new ResolveFreshVarMOS(context));
*/

         //fast rewriting related stuff
        /*
         * wiill need this in the future.
        steps.add(new ComputeCellsOfInterest(context));

        steps.add(new AddTopCellConfig(context));
        
        steps.add(new AddTopCellRules(context));
*/
        /*        need this in the future.

        steps.add(new ResolveBinder(context));
        steps.add(new ResolveAnonymousVariables(context));
        */
        //steps.add(new AddK2SMTLib(context));
        //steps.add(new ResolveSyntaxPredicates(context));
        //steps.add(new ResolveBuiltins(context));
        /*will need this in the future.
        steps.add(new ResolveListOfK(context));
        */
/* will need the following in the future.
       // steps.add(new FlattenSyntax(context));
        steps.add(new ResolveBlockingInput(context, kem));
        steps.add(new InitializeConfigurationStructure(context));
        //steps.add(new AddKStringConversion(context));
        //steps.add(new AddKLabelConstant(context));
        steps.add(new ResolveConfigurationAbstraction(context, kem));
        steps.add(new ResolveOpenCells(context));
        steps.add(new ResolveRewrite(context));

         //data structure related stuff 
        //steps.add(new CompileDataStructures(context, kem));
       /* steps.add(new JavaBackendCell2DataStructure(context));
        steps.add(new DataStructureToLookupUpdate(context));

        steps.add(new ResolveSupercool(context));
        steps.add(new AddStrictStar(context));
        steps.add(new AddDefaultComputational(context));
        steps.add(new AddOptionalTags(context));
        steps.add(new DeclareCellLabels(context));

        steps.add(new AddLocalRewritesUnderCells(context));
        steps.add(new GenerateKRewriteMachineInstructions(context));
        //steps.add(new LastStep(this, context));
*/
        return steps;
    }

    @Override
    public boolean generatesDefinition() {
        return true;
    }

    @Override
    public String autoincludedFile() {
        return Backends.AUTOINCLUDE_JAVA;
    }
}
