package org.kframework.kompile;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;

public class GeneratedHeatingCoolingRules extends CopyOnWriteTransformer {

    private static final String STRICT = "strict";
    private static final String SEQSTRICT = "seqstrict";
    private List<ModuleItem> items = new ArrayList<>();

    public GeneratedHeatingCoolingRules(Context context) {
        super("Strict Ops To Heating/Cooling Rules.", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        //collect the productions which have the attributes strict and seqstrict
        Set<Production> prods = SyntaxByTag.get(node, "strict", context);
        prods.addAll(SyntaxByTag.get(node, "seqstrict", context));
        if (prods.isEmpty()) {
            return node;
        }

        items = new ArrayList<>(node.getItems());
        node = node.shallowCopy();
        node.setItems(items);

        for (Production prod : prods) {
            assert prod.containsAttribute("strict") && !prod.containsAttribute("seqstrict")
                   || !prod.containsAttribute("strict") && prod.containsAttribute("seqstrict");
            Boolean isSeq = prod.containsAttribute("seqstrict");

            if (!(prod.getSort().isComputationSort() || prod.getSort().equals(Sort.KLABEL))) {
                throw KExceptionManager.compilerError(
                        "only productions of sort K, sort KLabel or of syntactic sorts can have "
                                + "strictness attributes",
                        this, prod);
            }

            if (prod.isSubsort()) {
                throw KExceptionManager.compilerError(
                        "Production is a subsort and cannot be strict.",
                        this, prod);
            }

            if (prod.isConstant() && !prod.getSort().equals(Sort.KLABEL)) {
                throw KExceptionManager.compilerError(
                        "Production is a constant and cannot be strict.",
                        this, prod);
            }

            final String strictType;
            if (!isSeq) {
                strictType = STRICT;
            } else {
                strictType = SEQSTRICT;
            }
            String attribute = prod.getAttribute(strictType);

            String[] strictAttrs = null;

            int arity = prod.getArityOfKItem();

            List<Integer> strictnessPositions = new ArrayList<>();
            if (attribute.isEmpty()) {
                for (int i = 1; i <= arity; i++) {
                    strictnessPositions.add(i);
                }
            } else {
                strictAttrs = attribute.split(",");
                for (String strictAttr : strictAttrs) {
                    try {
                        strictnessPositions.add(Integer.parseInt(strictAttr.trim()));
                    } catch (NumberFormatException e) {
                        throw KExceptionManager.compilerError(
                                "Expecting a number between 1 and " + arity + ", but found " + strictAttr + " as a" +
                                        " strict position in " + Arrays.toString(strictAttrs),
                                this, prod);
                    }
                }
            }

            for (int i = 0; i < strictnessPositions.size(); i++) {
            	
            	//generate heating rule first.
                KApp appHeatLeft = (KApp) MetaK.getTerm(prod, context);
                KApp appHeatRight = new KApp(appHeatLeft);
                KList listHeatLeft = (KList) appHeatLeft.getChild();
                KList listHeatRight = new KList((KList) appHeatLeft.getChild());
                appHeatRight.setChild(listHeatRight);

                if (context.kompileOptions.experimental.legacyKast) {
                    for (int j = 0; j < arity; ++j) {
                    	listHeatLeft.getContents().get(j).setSort(Sort.KITEM);
                    	listHeatRight.getContents().get(j).setSort(Sort.KITEM);
                    }
                }

                // insert HOLE instead of the term
                Term appHeatRedux = listHeatRight
                		.getContents().get(-1 + strictnessPositions.get(i));
                listHeatRight.getContents().set(-1 + strictnessPositions.get(i),
                        Hole.KITEM_HOLE);
                
                ArrayList<Term> seqListHeatRight = new ArrayList<Term>();
                
                seqListHeatRight.add(appHeatRedux);
                seqListHeatRight.add(appHeatRight);
                
                KSequence seqHeatRight = new KSequence(seqListHeatRight);


                // is seqstrict the elements before the argument should be KResult
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        Term argHeatLeft =
                        		listHeatLeft.getContents().get(-1 + strictnessPositions.get(j));
                        argHeatLeft.setSort(Sort.KRESULT);
                        Term argHeatRight =
                        		listHeatRight.getContents().get(-1 + strictnessPositions.get(j));
                        argHeatRight.setSort(Sort.KRESULT);

                    }
                }

                org.kframework.kil.Rule ctxHeat =
                		new org.kframework.kil.Rule(appHeatLeft,seqHeatRight,this.context);
                //ctx.setBody(app,app,this.context);
                ctxHeat.copyAttributesFrom(prod);
                ctxHeat.setLocation(prod.getLocation());
                ctxHeat.setSource(prod.getSource());
                ctxHeat.addAttribute("cell", "k");
                items.add(ctxHeat);
                
                
                //generate cooling rules
                KApp appCoolLeft = (KApp) MetaK.getTerm(prod, context);
                KApp appCoolRight = new KApp(appCoolLeft);
                KList listCoolLeft = (KList) appCoolLeft.getChild();
                KList listCoolRight = new KList((KList) appCoolLeft.getChild());
                appCoolRight.setChild(listCoolRight);

                if (context.kompileOptions.experimental.legacyKast) {
                    for (int j = 0; j < arity; ++j) {
                    	listCoolLeft.getContents().get(j).setSort(Sort.KITEM);
                    	listCoolRight.getContents().get(j).setSort(Sort.KITEM);
                    }
                }

                // insert HOLE instead of the term
                Term appCoolRedux = listCoolLeft
                		.getContents().get(-1 + strictnessPositions.get(i));
                appCoolRedux.setSort(Sort.KRESULT);
                listCoolLeft.getContents().set(-1 + strictnessPositions.get(i),
                        Hole.KITEM_HOLE);
                
                ArrayList<Term> seqListCoolLeft = new ArrayList<Term>();
                
                seqListCoolLeft.add(appCoolRedux);
                seqListCoolLeft.add(appCoolLeft);
                
                KSequence seqCoolLeft = new KSequence(seqListCoolLeft);


                // is seqstrict the elements before the argument should be KResult
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        Term argCoolLeft =
                        		listCoolLeft.getContents().get(-1 + strictnessPositions.get(j));
                        argCoolLeft.setSort(Sort.KRESULT);
                        Term argCoolRight =
                        		listCoolRight.getContents().get(-1 + strictnessPositions.get(j));
                        argCoolRight.setSort(Sort.KRESULT);

                    }
                }

                org.kframework.kil.Rule ctxCool =
                		new org.kframework.kil.Rule(seqCoolLeft,appCoolRight,this.context);
                //ctx.setBody(app,app,this.context);
                ctxCool.copyAttributesFrom(prod);
                ctxCool.setLocation(prod.getLocation());
                ctxCool.setSource(prod.getSource());
                ctxCool.addAttribute("cell", "k");
                items.add(ctxCool);
            }
        }

        return node;
    }
}
