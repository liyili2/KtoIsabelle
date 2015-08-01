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
	/*
	 * use for the counter for generated variables,
	 * constructor or labels.
	 */
	private int varCounter = 0;
	GlobalElement theElement;
	
	/*
	 * this map is related to the listSortMap, I guess
	 * the listSortMap and result map should be unified.
	 * it is mapping from the sort to the generated constructor
	 * for the sort.
	 * For example, we have the following case:
	 * syntax AExp ::= Int
	 * then we generate the constructor  Vaulue0
	 * if the varCounter is at 0, and increase the varCounter
	 * we need this because K allow people to input like:
	 * AExp ::= Int
	 * but Isabelle needs at least a constructor for it:
	 * AExp ::= Value0 Int
	 */
	Map<NonTerminal, String> resultMap;
	Set<String> labelSet;
	String inductiveName = "";
	
	/*
	 * this data is to have a collection of all builtin functions in K.
	 * apprently, builtin functions need to be translated into builtin
	 * functions in Isabelle.
	 */
	Set<String> builtinLabelSet;
	/*
	 * this map is actually have the same machanism as resultMap
	 * When we have list declaration syntax as:
	 * syntax Ids ::= List{Id,","}
	 * there is no such idea in Isabelle. What we need to translate
	 * to is like:
	 * type_synonym ids ::= "Id list"
	 * or we replace every position which we will have an Ids sort appeared
	 * to be Id list.
	 * In this printerToIsabelle file, we use the second way, that is, we replace
	 * every place of ids to be Id list.
	 * In order to do so, we need to keep a map from the sort:Ids to the Isabelle representation
	 * of it as: Id list. that is the job of the listSortMap
	 */
	Map<String, String> listSortMap;
	
	/*
	 * this map is for functions. 
	 * We will have a map from function klabels to function rules.
	 * In K, people don't divide rules into whehther or not it belongs
	 * to one function labels. 
	 * they view all rules are the same.
	 * When we translate it into Isabelle, we need to divide rules
	 * into different categories based on the left hand side function klabels.
	 */
	Map<String, List<Rule>> functionMap;
	
	public PrinterToIsabelle(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	//a constructor to generate the important information.
	public PrinterToIsabelle(Context context, GlobalElement element) {
		super(context);
		this.theElement = element;
		this.listSortMap = new HashMap<String, String>();
		this.functionMap = new HashMap<String, List<Rule>>();
		labelSet = new HashSet<String>();
		resultMap = new HashMap<NonTerminal, String>();
		ArrayList<NonTerminal> tempList = new ArrayList<NonTerminal>
		    (((Element)this.theElement).theMap.keySet());
		
		//generate all keys for resultmap.
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
	
	//this function will generate the name or variables based on the varCouonter
	//and then increase the varCounter.
	private String getGenVar(){
		varCounter ++;
		return "generatedVar"+varCounter;
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Term, java.lang.Object)
	 * this is a visitor case function.
	 * Since more terms we are looking for have super class Term
	 * we need to have a way to know its actual class is.
	 * This function is to discover the actual class of a given term and
	 * then direct those terms into its correct visitor function. 
	 */
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
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Definition, java.lang.Object)
     * This is the top of the visitor pattern.
     * It call the module visitor function because we will assume now we only have
     * one module in our definition.
     */
    public Void visit(Definition def, Void _void) {
        for (DefinitionItem item : def.getItems()) {
        	if(item instanceof Module){
        		this.visit((Module)item, _void);
        	}
        }
        return null;
    }
    
    /*
     * the meaning of the function is to make a
     * correct translation of a give sort in K
     * since some builtin sorts of K have different
     * name as the sorts of Isabelle. such as
     * Int in K will be int in Isabelle
     * Float in K will be real in Isabelle.
     * That is why we need this function
     * to print out the sort correctly for us.
     */
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
    /*
     * The datatype is actually the syntax in K
     * for example:
     * syntax AExp ::= goto(AExp,AExp) should be translated into 
     * datatype AExp = goto AExp AExp
     * 
     * However, there are small things to worry about.
     * 
     * First, we need to use a universal name generating machanism. 
     * 
     * in Isabelle, we can't use any symbols other than english characters and nums
     * for constructor. 
     * If a user has syntax AExp = AExp "/" AExp, then the klabel for it is '_/_
     * it is hard to translate to Isabelle since we can't use something like:
     * datatype AExp = '_/_ AExp AExp in Isabelle.
     * then, we will use the generateName function to generate the label as:
     * XDivX for the kabel, then the syntax become:
     * datatype AExp = XDivX AExp AExp in Isabelle.
     * 
     * In addition, we need to take care about the issues of recursive datatype.
     * In Isabelle, we are only allowed to have a datatype declare something which have
     * already existed. For example, K allows people to have:
     * syntax AExp ::= BExp "+" BExp
     * syntax BExp ::= AExp "&&" AExp
     * 
     * however you can use something like:
     * datatype AExp = Plus BExp BExp 
     * datatype BExp = And AExp AExp
     * in Isabelle. 
     * 
     * because in Isabelle, you can declare a datatype AExp to have BExp which at that point
     * it doesn't exist yet.
     * You must do something like:
     * datatype AExp = Plus BExp BExp
     * and BExp = And AExp AExp
     * 
     * In this file, we solve the problem by use and to connect all datatypes together.
     * 
     * Third, we need constructors for all productions in Isabelle:
     * In K, we can do something like:
     * syntax AExp ::= Int
     * 
     * In Isabelle, we are not allowed to do so. We must do something like:
     * syntax AExp ::= Value Int
     * I mean to add a construtor for it. 
     * We also need to remember the constructor we add and to use this constructor
     * in every place where the Int appears.
     * That is why in the code of printDatatype, we need to keep track of listSortMap
     * and resultMap
     */
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
    
    /*
     * this function is to print out all the KItems in Isabelle
     * In K, we have a implicit sort K and KItem.
     * In Isabelle, everything needs to be clear
     * That is why we need to print out the KItems.
     * such as:
     * datatype KItem =  AExpKItem AExp | BExpKItem BExp 
     *   | PgmKItem Pgm | BlockKItem Block | IdsKItem "Id list"
     * | StmtKItem Stmt | BoolKItem bool | IntKItem int | IdKItem Id
     * We need to know all the sorts in a definition in order to print out
     * a KItem constructor production for each sort.
     */
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
    
	/*
	 * this function takes a production and to generate a klabel
	 * for the input production.
	 * the way to generate the klabel is that
	 * we go through all the production item in the production, 
	 * and if a production item is terminal then we just put it
	 * into the string.
	 * if the production item is a nonterminal, then we use _ as
	 * the label and put it into the label string.
	 * in the production is a terminal or a nonTerminal.
	 * if the input production item is a terminal
	 */
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
    
	/*
	 * The two following functions need to be changed.
	 * These function is to get all the name of cells
	 * in a K Definition in order to print out them.
	 * For example, if we have the configuration for a
	 * definition in K:
	 *   configuration <T color="yellow">
     *             <k color="green"> $PGM:Pgm </k>
     *             <state color="red"> .Map </state>
     *           </T>
     * We need to collect all the names for each cell as
     * T, K, STATE,( we use upper cases for everythings)
     * In Isabelle, everything needs to be declare, we need to have a 
     * datatype for the name of these cells, such as
     * datatype CellLabel = T | K | STATE          
	 */
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
    
    /*
     * this function will actually printout the datatype for
     * cell names.
     */
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
    
    /*
     * Since all the function element has genereated in the getCodeInformation
     * class. this function will print out all the functions in Isabelle.
     * For example, in K we have:
     *   syntax Int ::= goto(Bool) [function]
     *   
     *     rule goto(true) => 1
     *     rule goto(A:Bool) => 0 [owise]
     *     
     * Hence, we need to print out like:
     * fun GotoBrXBr where
     * "(GotoBrXBr ( False )) = ( 1 ) "|
     * "(GotoBrXBr (A::bool)) = ( 0 )"
     * 
     * The function syntax in Isabelle is always like:
     * fun Name where
     * "Name input = output" |
     * "Name anotherinput = anotherout"
     * 
     * etc
     */
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
    
    /*
     * this function will change the name of symbols in K
     * to name of english characters in Isabelle.
     */
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

    /*
     * The visitor module function will
     * print out the datatypes by using printDatatype function
     * , printKItem function and printCellDatatype function.
     * then, it will genereate only one inductive rules for all the non-function
     * rules in K.
     */
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
    
    /*
     * This function will visit the list terminator in K
     * In K, List Terminator is really a class.
     * For example, in a rule like:
     * 
     * rule A => .K
     * 
     * the .K is really a list terminator. 
     * 
     * so that we need to do some translation like:
     * 
     * rule A ==> [] in Isabelle.
     * 
     */
    public Void visit(ListTerminator terminator, Void _void) {
        System.out.print("[]");
        return null;
    }
    
    /*
     *(non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Variable, java.lang.Object)
     * this visitor function will finish all the works for
     * translating a variable in K to a variable in Isabelle.
     * 
     * The way to do so is for a given variable like
     * A:KItem we will print out like:
     * (A::KItem)
     * In this example, A is the name for the variable and
     * KItem is the sort for the variable.
     */
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
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Rewrite, java.lang.Object)
     * K is kind of strange, a rewrite is a part of the rule.
     * it is actually the main part of the rules.
     * 
     * for example, if we have the rule like:
     * rule A => B when A =/= 0
     * 
     * then the A => B is the rewrite
     * The rewrite is calling the visitor for the LHS and the RHS
     * for the rules. 
     * 
     * for example if we have A => B rewrite
     * then we will call a function visitor to visit the LHS A and then
     * the RHS B.
     * A and B are assumed to be Cells in this file.
     */
    public Void visit(Rewrite rewrite, Void _void) {
        this.visit(rewrite.getLeft(), _void);
        System.out.println();
    	this.visit(rewrite.getRight(), _void);
    	return null;
    }
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Rule, java.lang.Object)
     * this is a visitor function to visit the rules.
     * 
     * It will call rewrite visit function for its rewrite body
     * and call othertings (Most likely KApp visitor function to check the
     * requires and ensures). 
     * In a rule, requires and ensures means the when part such as
     * rule A => B when C
     * requires and ensures mean the C.
     */
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
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Cell, java.lang.Object)
     * the cell will be the LHS and RHS of a rewrite.
     * In K we have something like:
     * <k> somethingA </k> => <k> somethingB </k>
     * when we translate it into Isabelle,
     * we need to do like:
     * (K, somethingA) ==> (K, somethingB)
     * In Isabelle you can never write like 
     * <abc> A </abc>
     * 
     * there is a problem we must solve in the function:
     * In K, people can write
     * <abc> A </abc> => <abc> B </abc>
     * and <k>B</k> <t>C</t> => <k>E</k> <t>F</t>
     * at the same time. 
     * In Isabelle, we must make sure that the LHS and RHS of every rule
     * will have the same type.
     * In the case above, we have a type of a cell abc in the first case
     * but we have two cells in LHS and RHS for the second rules.
     * 
     *  To solve this problem, we need to view everything is a list of cells
     *  in Isabelle. The first rule will be
     *  (abc, A)#[] => (abc,B)
     *  and the second rule will be
     *  (k, B)#((t,C)#[]) => (k, E)#((t,C)#[])
     *   
     */
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
