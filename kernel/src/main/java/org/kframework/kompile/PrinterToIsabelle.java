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
import org.kframework.kil.DataStructureSort;
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
import org.kframework.kil.Sort;
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
	Set<String> builtinLabelSet;
	Map<String, String> listSortMap;
	Map<String, List<Rule>> functionMap;
	
	public PrinterToIsabelle(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	public PrinterToIsabelle(Context context, GlobalElement element) {
		super(context);
		this.theElement = element;
		this.listSortMap = new HashMap<String, String>();
		this.functionMap = new HashMap<String, List<Rule>>();
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
		
		builtinLabelSet = new HashSet<String>();
		builtinLabelSet.add("'_+Int_");
		builtinLabelSet.add("'_*Int_");
		builtinLabelSet.add("'_-Int_");
		builtinLabelSet.add("'_%Int_");
		builtinLabelSet.add("'_divInt_");
		builtinLabelSet.add("'_modInt_");
		builtinLabelSet.add("'~Int_");
		builtinLabelSet.add("'_<=Int_");
		builtinLabelSet.add("'_<Int_");
		builtinLabelSet.add("'_>Int_");
		builtinLabelSet.add("'_>=Int_");
		builtinLabelSet.add("'_==Int_");
		builtinLabelSet.add("'_=/=Int_");
		builtinLabelSet.add("'notBool_");
		builtinLabelSet.add("'_andBool_");
		builtinLabelSet.add("'_andThenBool_");
		builtinLabelSet.add("'_xorBool_");
		builtinLabelSet.add("'_orBool_");
		builtinLabelSet.add("'_orElseBool_");
		builtinLabelSet.add("'_impliesBool_");
		builtinLabelSet.add("'_==Bool_");
		builtinLabelSet.add("'_=/=Bool_");
		builtinLabelSet.add("'_+String_");
		builtinLabelSet.add("'_==String_");
		builtinLabelSet.add("'_=/=String_");
		builtinLabelSet.add("'lengthString");
		builtinLabelSet.add("'substrString");
		builtinLabelSet.add("'Float2String");
		builtinLabelSet.add("'String2Float");
		builtinLabelSet.add("'String2Int");
		builtinLabelSet.add("'Int2String");
		builtinLabelSet.add("'--Float_");
		builtinLabelSet.add("'_^Float_");
		builtinLabelSet.add("'_*Float_");
		builtinLabelSet.add("'_+Float_");
		builtinLabelSet.add("'_-Float_");
		builtinLabelSet.add("'_/Float_");
		//builtinLabelSet.add("'_%Float_");
		builtinLabelSet.add("'_<=Float_");
		builtinLabelSet.add("'_<Float_");
		builtinLabelSet.add("'_>Float_");
		builtinLabelSet.add("'_>=Float_");
		builtinLabelSet.add("'_==Float_");
		builtinLabelSet.add("'_=/=Float_");
		builtinLabelSet.add("'keys(_)");
		builtinLabelSet.add("'_in_");
		builtinLabelSet.add("'size(_)");
		builtinLabelSet.add("'values(_)");
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
    
    private String correctSort(String name){
    	if(name.equals(Sort.INT.getName()))
    		return "int";
    	
    	if(name.equals(Sort.STRING.getName()))
    		return "string";
    	
    	if(name.equals(Sort.BOOL.getName()))
    		return "bool";
    	
    	if(name.equals(Sort.FLOAT.getName()))
    		return "real";
    	
    	if(this.listSortMap.containsKey(name))
    		return this.listSortMap.get(name);
    	
    	return name;
    }
    
    //this function print out all the datatype from theElement map.
    private void printDatatype(){
		ArrayList<NonTerminal> termList
            = new ArrayList<NonTerminal>(((Element)this.theElement).theMap.keySet());
		
		for(int index = 0; index < termList.size(); ++index) {
			if(((List<Production>)
		        	(((Element)this.theElement).theMap.get(termList.get(index)))).size() == 1
		        	&& ((List<Production>)
				        	(((Element)this.theElement).theMap
				        			.get(termList.get(index)))).get(0).isListDecl()){
        		this.listSortMap.put(termList.get(index)
        				.getName(), ((UserList)(((List<Production>)
    		        	(((Element)this.theElement).theMap.get(termList.get(index))))
    		        	.get(0).getListDecl())).getSort()+" list");
        	}
		}
		
        for(int index = 0; index < termList.size(); ++index) {
        	
        	if(!(((List<Production>)
		        	(((Element)this.theElement).theMap.get(termList.get(index)))).size() == 1
		        	&& ((List<Production>)
				        	(((Element)this.theElement).theMap
				        			.get(termList.get(index)))).get(0).isListDecl())){
        		if(index == 0){
        			System.out.print("datatype "+termList.get(index).getName()+" = ");
        		} else {
        			System.out.print("and "+termList.get(index).getName()+" = ");
        		}
    	        for(int i = 0; i < ((List<Production>)
    		        	(((Element)this.theElement).theMap
    		        			.get(termList.get(index)))).size(); ++i){
    	    	    Production t = ((List<Production>)
    			        	(((Element)this.theElement).theMap
    			        			.get(termList.get(index)))).get(i);
    	    	     if(t.getKLabel() == null && t.getItems().size() == 1){
    	    		    if(t.getItems().get(0) instanceof NonTerminal){
    	    		    	if(((NonTerminal)t.getItems().get(0)).getName().equals("Int")
    	    			    		|| ((NonTerminal)t.getItems().get(0))
    	    			    		.getName().equals("Bool")
    	    			    		|| ((NonTerminal)t.getItems().get(0))
    	    			    		.getName().equals("String")
    	    			    		|| ((NonTerminal)t.getItems().get(0))
    	    			    		.getName().equals("Float")){
    	    				    if(resultMap.keySet().contains(((NonTerminal)t.getItems().get(0)))){
    	    				    	if(resultMap.get(((NonTerminal)t.getItems().get(0))) == null){
    	    				    		resultMap.put(((NonTerminal)t.getItems().get(0)),
    	    				    				"Value"+this.varCounter);
    	    				    	}
    	    					    System.out.print(" Value"+this.varCounter+" ");
    	    				    } else {
    	    				    	System.out.print(" "
    	    				    +termList.get(index).getName()+this.varCounter+" ");
    	    				    }
    			    		    this.varCounter++;
    		    			    System.out.print(((NonTerminal)t.getItems().get(0))
    		    			    		.getName().toLowerCase()+" ");
    	    			     } else if(((NonTerminal)t.getItems().get(0))
    	    			    		.getName().equals("Id")){
    	    				    System.out.print(" "+
    	    			    		termList.get(index).getName()+"Id Id ");
    	    			    } else {
    	    				    if(resultMap.keySet().contains(((NonTerminal)t.getItems().get(0)))){
    	    				    	if(resultMap.get(((NonTerminal)t.getItems().get(0))) == null){
    	    				    		resultMap.put(((NonTerminal)t.getItems().get(0))
    	    				    				, "Value"+this.varCounter);
    	    				    	}
    	    					     System.out.print(" Value"+this.varCounter+" ");
    	    				     } else {
    	    					     System.out.print(" "
    	    				     +termList.get(index).getName()+this.varCounter+" ");
    	    				      }
    			    		    this.varCounter++;
    			    		    if(this.listSortMap.containsKey(((NonTerminal)t
    			    		    		.getItems().get(0)).getName())){
    			    		    	System.out.print("\""+this.listSortMap.get(((NonTerminal)t
    			    		    			.getItems().get(0)).getName())+"\" ");
    			    		    } else {
    			    		    	System.out.print(((NonTerminal)t
    			    		    			.getItems().get(0)).getName()+" ");
    			    		    }
    	    			    }
    	    		    }
    	    	    } else {
    	    		    System.out.print(" "+this.generateName(t.getKLabel().toString())+" ");
    		            for (int i1 = 0; i1 < t.getItems().size(); ++i1) {
    		                if (((ProductionItem) t.getItems().get(i1) instanceof NonTerminal)) {
    		                	if(this.listSortMap.containsKey(((NonTerminal) t
    		                			.getItems().get(i1)).getName()))
    		                		System.out.println("\""+this.listSortMap.get(((NonTerminal) t
        		                			.getItems().get(i1)).getName())+"\" ");
    		                	else
    		                	    System.out.print(((NonTerminal) t
    		                	    		.getItems().get(i1)).getName()+" ");
    		                }
    		            }
    	    	    }
    		        System.out.print("|");
    		    }
    	        System.out.print(" "+termList.get(index).getName()+"Hole ");
    	        System.out.println();
        	}
        }
    }
    
    private void printKItem(){
    	System.out.print("datatype KItem = ");
		ArrayList<NonTerminal> termList
        = new ArrayList<NonTerminal>(((Element)this.theElement).theMap.keySet());
		termList.addAll(this.resultMap.keySet());
        for(int i = 0; i < termList.size(); ++i){
        	if(this.listSortMap.containsKey(termList.get(i).getName()))
        		System.out.println(" "+termList.get(i).getName()+"KItem \""
        				+this.listSortMap.get(termList.get(i).getName())+"\" ");
        	else 
        	    System.out.print(" "+termList.get(i).getName()+"KItem "
                                           +correctSort(termList.get(i).getName())+" ");
            System.out.print("|");
        }
        System.out.println(" IdKItem Id");
        System.out.println("type_synonym K = \"KItem list\"");
    }
    
	private String generateKLabel(Production item){
		String label = "'";
		for(ProductionItem p : item.getItems()){
			if(!(p instanceof Terminal)){
				label += "_";
			} else {
				label += ((Terminal)p).getTerminal();
			}
		}
		return label;
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
    
    private void printCellDatatype(){
        System.out.print("datatype CellName = ");
        ArrayList<String> labelTempList = new ArrayList<String>(this.labelSet);
        for(int i = 0; i < labelTempList.size(); ++i){
        	System.out.print(" "+labelTempList.get(i)+" ");
        	if(i != labelTempList.size() - 1){
        		System.out.print("|");
        	}
        }
        System.out.println();
        System.out.println("datatype Cell = BagCell CellName \"Cell list\" |"
        		+"KCell CellName K | MapCell CellName Map "
        		+"| SetCell CellName Set | ListCell CellName List");
        System.out.println("type_synonym Bag = \"Cell list\"");
    }
    
    private void printFunctions(Void p){
        for(FunctionElement f : ((Element)this.theElement).functionDecls){
        	ArrayList<Rule> terms = (ArrayList<Rule>) this.functionMap.get(f.klabel);
        	System.out.println("fun "+this.generateName(f.klabel)+" where");
        	Rule owiseRule = null;
        	for(int i = 0; i < terms.size(); ++i){
        		if(terms.get(i).containsAttribute("owise")){
        			if(i == terms.size() - 1){
            			System.out.print("\"");
            			this.visit(((Rewrite)terms.get(i).getBody()).getLeft(), p);
            			System.out.print(" = ");
            			this.visit(((Rewrite)terms.get(i).getBody()).getRight(), p);
            			System.out.println("\"");
        			} else
        			    owiseRule = terms.get(i);
        		} else {
        			System.out.print("\"");
        			this.visit(((Rewrite)terms.get(i).getBody()).getLeft(), p);
        			System.out.print(" = ");
        			this.visit(((Rewrite)terms.get(i).getBody()).getRight(), p);
        			System.out.print("\"");
        			if(i != terms.size() - 1){
        				System.out.println("|");
        			}
        		}
        	}
        	
        	if(owiseRule != null){
    			System.out.print("|\"");
    			this.visit(((Rewrite)owiseRule.getBody()).getLeft(), p);
    			System.out.print(" = ");
    			this.visit(((Rewrite)owiseRule.getBody()).getRight(), p);
    			System.out.println("\"");
        	}
        }
    }
    
    private String generateName(String t){
    	
    	String value = "";
    	for(int i = 0; i < t.length(); ++i) {
    		if(t.charAt(i) == '\''){
    			if(i != 0) {
    				value += "Top";
    			}
    		} else if (t.charAt(i) == '_') {
    			value += "X";
    		} else if(t.charAt(i) == '(' || t.charAt(i) == ')') {
    			value += "Br";
    		} else if(t.charAt(i) == '{' || t.charAt(i) == '}') {
    			value += "Bl";
    		} else if(t.charAt(i) == '[' || t.charAt(i) == ']') {
    			value += "Bm";
    		} else if(t.charAt(i) == '=') {
    			value += "Eq";
    		} else if(t.charAt(i) == '|') {
    			value += "Sl";
    		} else if(t.charAt(i) == '&') {
    			value += "An";
    		} else if(t.charAt(i) == '@') {
    			value += "At";
    		} else if(t.charAt(i) == '*') {
    			value += "Times";
    		} else if(t.charAt(i) == '+') {
    			value += "Plus";
    		} else if(t.charAt(i) == '-') {
    			value += "Minus";
    		} else if(t.charAt(i) == '/') {
    			value += "Div";
    		} else if(t.charAt(i) == '<') {
    			value += "Less";
    		} else if(t.charAt(i) == '>') {
    			value += "Greater";
    		} else if(t.charAt(i) == '!') {
    			value += "Not";
    		} else if(t.charAt(i) == ';') {
    			value += "End";
    		} else if(t.charAt(i) == ':') {
    			value += "To";
    		} else {
    			value += t.charAt(i);
    		}
    	}
    	if(value.length() >= 1) {
    		if(value.charAt(0) <= 'z' && value.charAt(0) >= 'a') {
    			value = value.substring(0, 1).toUpperCase()
    					+ value.substring(1, value.length());
    		} else if(value.charAt(0) <= '9' && value.charAt(0) >= '0'){
    			value = "Num"+value;
    		}
    	}
    	return value;
    }

    
    public Void visit(Module mod, Void _void) {
        System.out.println("theory "+mod.getName().toUpperCase()+"\nimports Main Real");
        System.out.println("begin\n");
        
        System.out.println("datatype Id = TheId string");
        System.out.println("type_synonym Float = \"real\"");
        System.out.println("definition xor :: \"bool \\<Rightarrow> bool \\<Rightarrow> bool\""
        		+"(infixl \"[+]\" 60)");
        System.out.println("where \"A [+] B \\<equiv>"
        		+"(A \\<and> \\<not> B) \\<or> (\\<not> A \\<and> B)\"");
        printDatatype();
        printKItem();
        System.out.println("datatype MapItem = Mapsto KItem K");
        System.out.println("type_synonym Map = \"MapItem list\"");
        System.out.println("datatype SetElem = SetItem K");
        System.out.println("type_synonym Set = \"SetElem list\"");
        System.out.println("datatype ListElem = ListItem K");
        System.out.println("type_synonym List = \"ListElem list\"");
        System.out.println("fun keys :: \"Map \\<Rightarrow> KItem set\" where\n"
                            +"\"keys [] = {}\"\n|\"keys ((Mapsto A B)#l) "
        		            +"= insert A (keys l)\"");
        System.out.println("fun theValues :: \"Map \\<Rightarrow> K set\" where\n"
                +"\"theValues [] = {}\"\n|\"theValues ((Mapsto A B)#l) "
	            +"= insert B (theValues l)\"");
        System.out.println("fun kSetToSet :: \"Set \\<Rightarrow> K set\" where\n"
                +"\"kSetToSet [] = {}\"\n|\"kSetToSet ((SetItem A) #l) "
	            +"= insert A (kSetToSet l)\"");
        
        this.inductiveName = mod.getName().toLowerCase();
        
        ArrayList<Rule> ruleList = new ArrayList<Rule>();
        for(ModuleItem item : mod.getItems()){
        	if(item instanceof Rule){
            	if(((Rule)item).getBody() instanceof Rewrite){
            		if((((Rewrite)(((Rule)item).getBody())).getLeft() instanceof Cell)){
            			ruleList.add((Rule)item);
            		} else if(((Rewrite)(((Rule)item)
            				.getBody())).getLeft() instanceof TermCons
            				&& ((Rule)item).containsAttribute("function")){
            			String theLabel = this.generateKLabel(((TermCons)
            					((Rewrite)(((Rule)item).
            							getBody())).getLeft()).getProduction());
            			if(this.functionMap.containsKey(theLabel)){
            				this.functionMap.get(theLabel).add((Rule)item);
            			} else {
            				ArrayList<Rule> resultRules = new ArrayList<Rule>();
            				resultRules.add((Rule)item);
            				this.functionMap.put(theLabel, resultRules);
            			}            			
            		}
            	}
        	} else if(item instanceof Configuration){
        		generateCellLabels((Cell)((Configuration)item).getBody());
        	}
        }
        
        //print out the label set labels as a datatype
        printCellDatatype();
        System.out.println();
        printFunctions(_void);
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
        System.out.print(variable.getName()
        		+"::" + this.correctSort(variable.getSort().toString()));
        System.out.print(")");
        return null;
    }
    
    public Void visit(Rewrite rewrite, Void _void) {
        this.visit(rewrite.getLeft(), _void);
        System.out.println();
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
    
    public Void visit(Cell cell, Void _void) {
    	String value = "(";
    	if(cell.getContents() instanceof Cell
    			|| cell.getContents() instanceof Bag){
    		value += "BagCell " + cell.getLabel().toUpperCase()+" (";
    	} else if(cell.getContents().getSort().equals(Sort.MAP)){
    		value += "MapCell " + cell.getLabel().toUpperCase()+" (";
    	} else if(cell.getContents().getSort().equals(Sort.LIST)){
    		value += "ListCell " + cell.getLabel().toUpperCase()+" (";
    	} else if(cell.getContents().getSort().equals(Sort.SET)){
    		value += "SetCell " + cell.getLabel().toUpperCase()+" (";
    	} else {
    		value += "KCell " + cell.getLabel().toUpperCase()+" (";
    		System.out.print(value);
    		if(cell.getContents().getSort().equals(Sort.KITEM)){
    			this.visit(cell.getContents(), _void);
        		System.out.print(" # []))");
    		} else if(cell.getContents().getSort().equals(Sort.K)){
    			this.visit(cell.getContents(), _void);
        		System.out.print("))");
    		} else {
    			System.out.println(cell.getContents().getSort().getName()+"KItem ");
    			this.visit(cell.getContents(), _void);
        		System.out.print(" # []))");
    		}
    		return null;
    	}
        System.out.print(value);
        //if (cell.hasLeftEllipsis()) {
        //    System.out.print(this.getGenVar()+"# ");
        //}
        this.visit(cell.getContents(), _void);
        //if (cell.hasRightEllipsis()) {
         //   System.out.print(" #"+this.getGenVar());
        //}
        System.out.print("))");
        return null;
    }
    
    public Void visit(Bag bag, Void _void) {
        for (int i = 0; i < bag.getContents().size(); ++i) {
            this.visit((Term)(bag.getContents().get(i)), _void);
            if(i != bag.getContents().size() - 1){
            	System.out.println(" # ");
            }
        }
        if (bag.getContents().size() == 0) {
            System.out.print("[]");
        } else if(!((bag.getContents().get(bag.getContents().size() - 1) instanceof Bag &&
        		((Bag)bag.getContents()).getContents().size() == 0) ||
        		(bag.getContents().get(bag.getContents().size() - 1) instanceof Variable &&
        				((Variable)bag.getContents().get(bag.getContents().size() - 1))
        				.getSort().equals(Sort.BAG)) ||
        				(bag.getContents().get(bag.getContents().size() - 1) instanceof Cell
        	&& ((Cell)bag.getContents().get(bag.getContents().size() - 1)).getContents() instanceof Variable
        	&& ((Variable)((Cell)bag.getContents().get(bag.getContents().size() - 1))
        			.getContents()).getSort().equals(Sort.BAG)))){
        	System.out.println(" # []");
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
    	if(kapp.getLabel() instanceof KLabelConstant
    			&& ((KLabelConstant)kapp.getLabel()).getLabel()
    			.equals(DataStructureSort.DEFAULT_MAP_LABEL)){
    		if(kapp.getChild() instanceof KList){
    			for(int i = 0; i< ((KList)kapp.getChild())
    					.getContents().size(); ++i){
    				this.visit((Term) ((KList)kapp.getChild())
        					.getContents().get(i), _void);
    				if(i != ((KList)kapp.getChild())
    					.getContents().size() - 1){
    					System.out.print(" # ");
    				}
    			}
    		}
    	} else {
            this.visit(kapp.getLabel(), _void);
            if (!(kapp.getLabel() instanceof Token) && !(kapp.getLabel() instanceof KInjectedLabel)) {
                System.out.print(" ");
                this.visit(kapp.getChild(), _void);
            }
    	}
        System.out.println(")");
        return null;
    }
    
    public Void visit(KLabelConstant kLabelConstant, Void _void) {
        System.out.print(this.generateName(kLabelConstant.getLabel()));
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
            	System.out.println(contents.get(i).getClass()+","+contents.get(i).getSort());
            	if(contents.get(i).getSort().equals(Sort.KITEM)
            			|| contents.get(i).getSort().equals(Sort.K)){
            		this.visit(contents.get(i), _void);
            	} else {
            		System.out.print("("+contents.get(i).getSort().getName()+"KItem ");
            		this.visit(contents.get(i), _void);
            		System.out.print(")");
            	}
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
    
    private void dealWithBuiltins(ArrayList<Term> termList, String label, Void p){
    	if(label.equals("'_+Int_") || label.equals("'_+Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" + ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_-Int_") || label.equals("'_-Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" - ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_*Int_") || label.equals("'_*Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" * ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_/Int_") || label.equals("'_divInt_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" div ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_%Int_") || label.equals("'_modInt_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" mod ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'~Int_") || label.equals("'--Float_")){
    		System.out.print("(");
    		System.out.print("- ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'_<=Int_") || label.equals("'_<=Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<le> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_<Int_") || label.equals("'_<Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" < ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_>Int_") || label.equals("'_>Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" > ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_>=Int_") || label.equals("'_>=Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<ge> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_==Int_") || label.equals("'_==Bool_")
    			|| label.equals("'_==String_") || label.equals("'_==Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" = ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_=/=Int_") || label.equals("'_=/=Bool_")
    			|| label.equals("'_=/=String_") || label.equals("'_=/=Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<noteq> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'notBool_")){
    		System.out.print("(");
    		System.out.print(" \\<not> ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'_andBool_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<and> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_andThenBool_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<and> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_xorBool_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" [+] ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_orElseBool_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<or> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_impliesBool_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<longrightarrow> ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_+String_")){
    		System.out.print("(concat [");
    		this.visit(termList.get(0), p);
    		System.out.print(", ");
    		this.visit(termList.get(1), p);
    		System.out.println("])");
    	} else if(label.equals("'lengthString")){
    		System.out.print("(length ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'substrString")){
    		System.out.print("(sublist ");
    		this.visit(termList.get(0), p);
    		System.out.print(" {");
    		this.visit(termList.get(1), p);
    		System.out.print(" .. ");
    		this.visit(termList.get(2), p);
    		System.out.println("})");
    	} else if(label.equals("'String2Int")){
    		System.out.print("(length ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'_^Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" ^ ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'_/Float_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" / ");
    		this.visit(termList.get(1), p);
    		System.out.println(")");
    	} else if(label.equals("'size(_)")){
    		System.out.print("(length ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'keys(_)")){
    		System.out.print("(keys ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'values(_)")){
    		System.out.print("(theValues ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	} else if(label.equals("'_in_")){
    		System.out.print("(");
    		this.visit(termList.get(0), p);
    		System.out.print(" \\<in> kSetToSet ");
    		this.visit(termList.get(0), p);
    		System.out.println(")");
    	}
    }
    
    public Void visit(TermCons termCons, Void _void) {
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = "'_"+userList.getSeparator()+"_";
            java.util.List<Term> contents = termCons.getContents();
            System.out.print("("+this.generateName(separator)+" ");
            this.visit(contents.get(0), _void);
            System.out.print(" ");
            this.visit(contents.get(1), _void);
            System.out.print(")");
        } else {
            int where = 0;
            String label = "'";
            ArrayList<Term> termList = new ArrayList<Term>();
            Term lastVar = null;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = (ProductionItem) production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    Term subterm = (Term) termCons.getContents().get(where);
                    if(termCons.getSort().equals(Sort.MAP) 
                    		&& (subterm instanceof Variable)){
                    	lastVar = subterm;
                    } else {
                        termList.add(subterm);
                    }
                    label += "_";
                    where++;
                } else {
                	label += ((Terminal) productionItem).getTerminal();
                }
            }
            
            if(lastVar != null){
            	termList.add(lastVar);
            }
            
            if(this.builtinLabelSet.contains(label)){
            	dealWithBuiltins(termList,label, _void);
            } else if(termCons.getSort().equals(Sort.MAP)) {
            	if(label.equals("'__")) {
            		System.out.print("(");
            		for(int i = 0; i < termList.size(); ++i){
            			if(!(lastVar != null && termList.get(i) instanceof TermCons
            					&& ((TermCons)termList.get(i)).getSort().equals(Sort.MAP)
            					&& ((TermCons)termList.get(i)).getProduction()
            					.getKLabel().equals(DataStructureSort.DEFAULT_MAP_UNIT_LABEL))){
            				this.visit(termList.get(i), _void);
            				if(i != termList.size() - 1){
                        		System.out.println(" # ");
                        	}
            			}
                    }
                    if(termList.size() == 0){
                    	System.out.print("[]");
                    }
                    System.out.print(")");
            	} else if(label.equals(DataStructureSort.DEFAULT_MAP_UNIT_LABEL)) {
            		System.out.println("[]");
            	} else if(label.equals(DataStructureSort.DEFAULT_MAP_ITEM_LABEL)){
            		System.out.print("(");
            		System.out.println("Mapsto");
                    for(int i = 0; i < termList.size(); ++i){
                    	System.out.print(" "+termList.get(i).getClass());
                    	System.out.print(" ");
                    	this.visit(termList.get(i), _void);
                    }
                    System.out.print(")");
            	}
            } else {
            	System.out.print("("+this.generateName(label));
                for(int i = 0; i < termList.size(); ++i){
                	System.out.print(" ");
                	this.visit(termList.get(i), _void);
                }
                System.out.print(")");

            }
        }
        return null;
    }
}
