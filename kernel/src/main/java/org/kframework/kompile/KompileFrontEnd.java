// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.backend.Backend;
import org.kframework.builtin.Sorts;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.CountNodesVisitor;
import org.kframework.main.FrontEnd;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

public class KompileFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KompileModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }


    private final Context context;
    private final KompileOptions options;
    private final Provider<Backend> backend;
    private final Provider<Consumer<CompiledDefinition>> koreBackend;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final Provider<DefinitionLoader> defLoader;
    private final FileUtil files;

    @Inject
    KompileFrontEnd(
            Context context,
            KompileOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Provider<Backend> backend,
            Provider<Consumer<CompiledDefinition>> koreBackend,
            Stopwatch sw,
            KExceptionManager kem,
            BinaryLoader loader,
            Provider<DefinitionLoader> defLoader,
            JarInfo jarInfo,
            FileUtil files) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.context = context;
        this.options = options;
        this.backend = backend;
        this.koreBackend = koreBackend;
        this.sw = sw;
        this.kem = kem;
        this.loader = loader;
        this.defLoader = defLoader;
        this.files = files;
    }

    @Override
    public int run() {
        if (!options.mainDefinitionFile().exists()) {
            throw KEMException.criticalError("Definition file doesn't exist: " +
                    options.mainDefinitionFile().getAbsolutePath());
        }

        if (options.experimental.kore) {
            Kompile kompile = new Kompile(options, files, kem, sw);
            //TODO(dwightguth): handle start symbols
            CompiledDefinition def = kompile.run(options.mainDefinitionFile(), options.mainModule(), options.syntaxModule(), Sorts.K());
            loader.saveOrDie(files.resolveKompiled("compiled.bin"), def);
            koreBackend.get().accept(def);
            sw.printIntermediate("Save to disk");
        } else {

            context.kompileOptions = options;

            Definition def = genericCompile(options.experimental.step);

            loader.saveOrDie(files.resolveKompiled("context.bin"), context);
            loader.saveOrDie(files.resolveKompiled("definition.bin"), def);
            verbose(def);
        }
        sw.printTotal("Total");
        return 0;
    }

    private void verbose(Definition def) {
        if (context.globalOptions.verbose) {
            CountNodesVisitor visitor = new CountNodesVisitor();
            visitor.visitNode(def);
            visitor.printStatistics();
        }
    }

    private Definition genericCompile(String step) {
        org.kframework.kil.Definition javaDef;
        sw.start();
        javaDef = defLoader.get().loadDefinition(options.mainDefinitionFile(), options.mainModule(),
                context);
        
        loader.saveOrDie(files.resolveKompiled("definition-concrete.bin"), javaDef);

        Backend b = backend.get();
        CompilerSteps<Definition> steps = b.getCompilationSteps();

        /*
        ArrayList abc = (ArrayList) javaDef.getItems();
        List<org.kframework.kil.DefinitionItem> newList = new ArrayList<>();
        for(int i = 0; i < abc.size();++i){
        	if(abc.get(i) instanceof org.kframework.kil.Module){
        		if(((org.kframework.kil.Module)abc.get(i)).getName().equals(javaDef.getMainModule())){
        			newList.add((DefinitionItem) abc.get(i));
        		}
        	}
        }
        javaDef.setItems(newList);
        */
        if (step == null) {
            step = b.getDefaultStep();
        }
        try {
            javaDef = steps.compile(javaDef, step);
        } catch (CompilerStepDone e) {
            javaDef = (Definition) e.getResult();
        }
        System.out.println(javaDef.toString());
        /*
        GetCodeInformation theGetter = new GetCodeInformation(context);
        GlobalElement theElement = theGetter.visit(javaDef);
        //System.out.println(((Element)theElement).kResultProductions);
        //System.out.println(javaDef.toString());
         * 
         */
        //System.exit(0);
        //System.out.println("Generated code is:"+((Element)theElement).theMap.toString());
        //System.out.println(step);
        //PrinterToIsabelle printer = new PrinterToIsabelle(context, theElement);
        //printer.visit(javaDef, null);
        System.exit(0);
        loader.saveOrDie(files.resolveKompiled("configuration.bin"),
                MetaK.getConfiguration(javaDef, context));

        b.run(javaDef);

        return javaDef;
    }
}

