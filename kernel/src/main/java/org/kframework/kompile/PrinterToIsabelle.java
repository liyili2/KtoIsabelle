package org.kframework.kompile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.utils.ColorUtil;

import com.sun.org.apache.xpath.internal.operations.Mod;

public class PrinterToIsabelle extends NonCachingVisitor {

	private int counter = 0;
	private int varCounter = 0;
	GlobalElement theElement;
	Map<NonTerminal, String> resultMap;
	Set<String> labelSet;
	String inductiveName = "";
	
	public PrinterToIsabelle(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	public PrinterToIsabelle(Context context, GlobalElement element) {
		super(context);
		this.theElement = element;
		labelSet = new HashSet<String>();
		resultMap = new HashMap<NonTerminal, String>();
		ArrayList<NonTerminal> tempList = new ArrayList<NonTerminal>
		    (((Element)this.theElement).theMap.keySet());
		for(NonTerminal n : tempList){
			if(n.getName().equals("KResult")){
				List<Production> prodList = (List<Production>) ((Element)this.theElement).theMap.get(n);
				for(int i = 0; i < prodList.size(); ++i){
					if(prodList.get(i).getItems().size() == 1
							&& prodList.get(i).getItems().get(0) instanceof NonTerminal){
						resultMap.put(((NonTerminal) prodList.get(i).getItems().get(0)), null);
					}
				}
				((Element)this.theElement).theMap.remove(n);
			}
		}
	}
	
	private String getGenVar(){
		varCounter ++;
		return "generatedVar"+varCounter;
	}
	
    public Void visit(Term node, Void _void) {
    	if(node instanceof Rewrite){
    		this.visit((Rewrite)node, _void);
    	} else if(node instanceof Cell){
    		this.visit((Cell)node, _void);
    	} else if(node instanceof KApp){
    		this.visit((KApp)node, _void);
    	} else if(node instanceof Bag){
    		this.visit((Bag)node, _void);
    	} else if(node instanceof TermCons){
    		this.visit((TermCons)node, _void);
    	} else if(node instanceof KSequence) {
    		this.visit((KSequence)node, _void);
    	} else if(node instanceof Variable){
    		this.visit((Variable)node, _void);
    	} else if(node instanceof ListTerminator){
    		this.visit((ListTerminator)node, _void);
    	} else if(node instanceof KLabelConstant){
    		this.visit((KLabelConstant)node, _void);
    	} else if(node instanceof IntBuiltin){
    		this.visit((IntBuiltin)node, _void);
    	} else if(node instanceof StringBuiltin){
    		this.visit((StringBuiltin)node, _void);
    	} else if(node instanceof FloatBuiltin){
    		this.visit((FloatBuiltin)node, _void);
    	} else if(node instanceof BoolBuiltin){
    		this.visit((BoolBuiltin)node, _void);
    	} else if(node instanceof KList){
    		this.visit((KList)node, _void);
    	} else if(node instanceof MapBuiltin){
    		this.visit((MapBuiltin)node, _void);
    	} else if(node instanceof SetBuiltin){
    		this.visit((SetBuiltin)node, _void);
    	} else if(node instanceof ListBuiltin){
    		this.visit((ListBuiltin)node, _void);
    	}
    	return null;
    }
    
    public Void visit(Definition def, Void _void) {
        for (DefinitionItem item : def.getItems()) {
        	if(item instanceof Module){
        		this.visit((Module)item, _void);
        	}
        }
        return null;
    }
    
    //this function print out all the datatype from theElement map.
    private void printDatatype(){
		ArrayList<NonTerminal> termList
            = new ArrayList<NonTerminal>(((Element)this.theElement).theMap.keySet());
        for(NonTerminal item : termList){
	        System.out.println("datatype "+item.getName()+" = ");
	        for(int i = 0; i < ((List<Production>)
		        	(((Element)this.theElement).theMap.get(item))).size(); ++i){
	    	    Production t = ((List<Production>)
			        	(((Element)this.theElement).theMap.get(item))).get(i);
	    	     if(t.getKLabel() == null && t.getItems().size() == 1){
	    		    if(t.getItems().get(0) instanceof NonTerminal){
	    		    	if(((NonTerminal)t.getItems().get(0)).getName().equals("Int")
	    			    		|| ((NonTerminal)t.getItems().get(0))
	    			    		.getName().equals("Bool")){
	    				    if(resultMap.keySet().contains(((NonTerminal)t.getItems().get(0)))){
	    				    	if(resultMap.get(((NonTerminal)t.getItems().get(0))) == null){
	    				    		resultMap
	    				    		.put(((NonTerminal)t.getItems().get(0)), "Value"+this.varCounter);
	    				    	}
	    					    System.out.print(" Value"+this.varCounter+" ");
	    				    } else {
	    				    	System.out.print(" "+item.getName()+this.varCounter+" ");
	    				    }
			    		    this.varCounter++;
		    			    System.out.print(((NonTerminal)t.getItems().get(0))
		    			    		.getName().toLowerCase()+" ");
	    			     } else if(((NonTerminal)t.getItems().get(0))
	    			    		.getName().equals("Id")){
	    				    System.out.print(" Id Int ");
	    			    } else {
	    				    if(resultMap.keySet().contains(((NonTerminal)t.getItems().get(0)))){
	    				    	if(resultMap.get(((NonTerminal)t.getItems().get(0))) == null){
	    				    		resultMap
	    				    		.put(((NonTerminal)t.getItems().get(0)), "Value"+this.varCounter);
	    				    	}
	    					     System.out.print(" Value"+this.varCounter+" ");
	    				     } else {
	    					     System.out.print(" "+item.getName()+this.varCounter+" ");
	    				      }
			    		      this.varCounter++;
		    			    System.out.print(((NonTerminal)t.getItems().get(0)).getName());
	    			    }
	    		    }
	    	    } else {
	    		    System.out.print(" "+t.getKLabel().toString()+" ");
		            for (int i1 = 0; i1 < t.getItems().size(); ++i1) {
		                if (((ProductionItem) t.getItems().get(i1) instanceof NonTerminal)) {
		                	System.out.print(((NonTerminal) t.getItems().get(i1)).getName()+" ");
		                }
		            }
	    	    }
		        System.out.print("|");
		    }
	        System.out.print(" "+item.getName()+"Hole ");
	        System.out.println();
        }
    }
    
    private void printKItem(){
    	System.out.print("datatype KItem = ");
		ArrayList<NonTerminal> termList
        = new ArrayList<NonTerminal>(((Element)this.theElement).theMap.keySet());
        for(int i = 0; i < termList.size(); ++i){
        	System.out.print(" "+termList.get(i).getName()+"KItem ");
        	if(i != termList.size() - 1){
        		System.out.print("|");
        	}
        }
        System.out.println();
        System.out.println("type_synonym 'var K = \"'var kItem list\"");
    }
    
    private void generateCellLabels(Cell t){
    	this.labelSet.add(t.getLabel().toUpperCase());
    	if(t.getContents() instanceof Bag){
    		generateCellLabels((Bag)t.getContents());
    	} else if (t.getContents() instanceof Cell){
    		generateCellLabels((Cell)t.getContents());
    	}
    }
    
    private void generateCellLabels(Bag t){
    	for(int i = 0; i < t.getContents().size(); ++i){
    		if(t.getContents().get(i) instanceof Cell){
    			generateCellLabels((Cell)t.getContents().get(i));
    		} else if(t.getContents().get(i) instanceof Bag){
    			generateCellLabels((Bag)t.getContents().get(i));
    		}
    	}
    }

    
    public Void visit(Module mod, Void _void) {
        System.out.println("theory "+mod.getName().toUpperCase()+"\nimports Main");
        System.out.println("begin\n");
        printDatatype();
        printKItem();
        this.inductiveName = mod.getName().toLowerCase();
        
        ArrayList<Rule> ruleList = new ArrayList<Rule>();
        for(ModuleItem item : mod.getItems()){
        	if(item instanceof Rule){
            	if(((Rule)item).getBody() instanceof Rewrite){
            		if((((Rewrite)(((Rule)item).getBody())).getLeft() instanceof Cell)){
            			ruleList.add((Rule)item);
            		}
            	}
        	} else if(item instanceof Configuration){
        		generateCellLabels((Cell)((Configuration)item).getBody());
        	}
        }
        
        //print out the label set labels as a datatype
        System.out.print(" datatype GeneratedLabel = ");
        ArrayList<String> labelTempList = new ArrayList<String>(this.labelSet);
        for(int i = 0; i < labelTempList.size(); ++i){
        	System.out.print(" "+labelTempList.get(i)+" ");
        	if(i != labelTempList.size() - 1){
        		System.out.print("|");
        	}
        }
        
        System.out.println();
        System.out.println("inductive "+this.inductiveName+"TheRule where");
        for (int i = 0; i < ruleList.size(); ++i) {
            //System.out.println(item.getClass());
        	this.visit(ruleList.get(i), _void);
        	if(i != ruleList.size() - 1){
        		System.out.print("| ");
        	}
        }
        System.out.println("\nend");
        return null;
    }
    
    public Void visit(ListTerminator terminator, Void _void) {
        System.out.print("[]");
        return null;
    }
    
    public Void visit(Variable variable, Void _void) {
    	System.out.print("(");
        if (variable.isFreshVariable())
            System.out.print("?");
        else if (variable.isFreshConstant())
        	System.out.print("!");
        System.out.print(variable.getName());
        System.out.print("::" + variable.getSort());
        System.out.print(")");
        return null;
    }
    
    public Void visit(Rewrite rewrite, Void _void) {
        this.visit(rewrite.getLeft(), _void);
        System.out.print(" ");
    	this.visit(rewrite.getRight(), _void);
    	return null;
    }
    
    public Void visit(Rule rule, Void _void) {
    	System.out.print("rule" + this.counter + ": \"");
    	this.counter++;
        if (rule.getRequires() != null) {
        	System.out.print(" ");
        	this.visit(rule.getRequires(), _void);
        	System.out.println("  \\<Longrightarrow> ");
        }
        if (rule.getEnsures() != null) {
        	System.out.print(" ");
        	this.visit(rule.getEnsures(), _void);
        	System.out.println("  \\<Longrightarrow> ");

        }
    	System.out.print(" "+this.inductiveName+"TheRule ");
        this.visit(rule.getBody(), _void);
        System.out.println("\"");
        return null;
    }
    
    public Void visit(Collection collection, Void _void) {
        java.util.List<Term> contents = collection.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            this.visit(contents.get(i), _void);
        }
        if (contents.size() == 0) {
            System.out.print("[]");
        }
        return null;
    }
    
    public Void visit(Cell cell, Void _void) {
        System.out.print("(" + cell.getLabel().toUpperCase()+", ");
        if (cell.hasLeftEllipsis()) {
            System.out.print(this.getGenVar()+"# ");
        }
        this.visit(cell.getContents(), _void);
        if (cell.hasRightEllipsis()) {
            System.out.print(" #"+this.getGenVar());
        }
        System.out.print(")");
        return null;
    }
    
    public Void visit(Bag bag, Void _void) {
        for (int i = 0; i < bag.getContents().size(); ++i) {
            this.visit((Term)(bag.getContents().get(i)), _void);
            if(i != bag.getContents().size() - 1){
            	System.out.println(" # ");
            }
        }
        return null;
    }
    
    public Void visit(KList listOfK, Void _void) {
        java.util.List<Term> termList = listOfK.getContents();
        for (int i = 0; i < termList.size(); ++i) {
            this.visit(termList.get(i), _void);
            if (i != termList.size() - 1) {
                System.out.println(" ");
            }
        }
        if (termList.size() == 0) {
        	System.out.println("");
        }
        return null;
    }
    
    public Void visit(KApp kapp, Void _void) {
    	System.out.print("(");
        this.visit(kapp.getLabel(), _void);
        if (!(kapp.getLabel() instanceof Token) && !(kapp.getLabel() instanceof KInjectedLabel)) {
            System.out.print(" ");
            this.visit(kapp.getChild(), _void);
            System.out.println(")");
        } else {
        	System.out.println(")");
        }
        return null;
    }
    
    public Void visit(KLabelConstant kLabelConstant, Void _void) {
        System.out.print(kLabelConstant.getLabel());
        return null;
    }
    
    public Void visit(KSequence ksequence, Void _void) {
        java.util.List<Term> contents = ksequence.getContents();
        System.out.print("(");
        if (!contents.isEmpty()) {
            for (int i = 0; i < contents.size(); i++) {
            	if(i == 0 && contents.get(i) instanceof KSequence){
            		if(((KSequence)contents.get(i)).getContents().isEmpty()){
            			System.out.print("[]");
            			break;
            		}
            	}
                this.visit(contents.get(i), _void);
                if (i != contents.size() - 1) {
                	System.out.print(" # ");
                }
            }
        } else {
        	System.out.print("[]");
        }
        System.out.print(")");
        return null;
    }
    
    public Void visit(ListBuiltin node, Void p) throws RuntimeException {
        for (Term t : node.elementsLeft()) {
            this.visit(t, p);
        }
        for (Term t : node.baseTerms()) {
            this.visit(t, p);
        }
        for (Term t : node.elementsRight()) {
            this.visit(t, p);
        }
        return null;
    }

    public Void visit(MapBuiltin node, Void p) throws RuntimeException {
        for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
            this.visit(entry.getKey(), p);
            this.visit(entry.getValue(), p);
        }
        for (Term t : node.baseTerms()) {
        	this.visit(t, p);
        }
        return null;
    }

    public Void visit(SetBuiltin node, Void p) throws RuntimeException {
        for (Term t : node.elements()) {
        	this.visit(t, p);
        }
        for (Term t : node.baseTerms()) {
        	this.visit(t, p);
        }
        return null;
    }
    
    public Void visit(IntBuiltin node, Void p) {
    	System.out.print(" "+node.value()+" ");
        return null;
    }
    
    public Void visit(StringBuiltin node, Void p) {
    	System.out.print(""+node.value()+"\" ");
        return null;
    }
    
    public Void visit(FloatBuiltin node, Void p) {
    	System.out.print(node.value());
        return null;
    }
    
    public Void visit(BoolBuiltin node, Void p) {
    	if(node.value().equals(BoolBuiltin.TRUE)){
    		System.out.print(" True ");
    	} else {
    		System.out.print(" False ");
    	}
        return null;
    }
    
    public Void visit(TermCons termCons, Void _void) {
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = "'_"+userList.getSeparator()+"_";
            java.util.List<Term> contents = termCons.getContents();
            System.out.print("("+separator+" ");
            this.visit(contents.get(0), _void);
            System.out.print(" ");
            this.visit(contents.get(1), _void);
            System.out.print(")");
        } else {
            int where = 0;
            String label = "'";
            ArrayList<Term> termList = new ArrayList<Term>();
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = (ProductionItem) production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    Term subterm = (Term) termCons.getContents().get(where);
                    termList.add(subterm);
                    label += "_";
                    where++;
                } else {
                	label += ((Terminal) productionItem).getTerminal();
                }
            }
            System.out.print("("+label);
            for(int i = 0; i < termList.size(); ++i){
            	System.out.print(" ");
            	this.visit(termList.get(i), _void);
            }
            System.out.print(")");
        }
        return null;
    }
}
