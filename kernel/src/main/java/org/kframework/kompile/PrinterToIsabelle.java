package org.kframework.kompile;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.Configuration;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.Import;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Syntax;
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
	Map<Sort, String> resultMap;
	Map<Sort, String> kitemMap;

	Set<String> labelSet;
	String inductiveName = "";
	
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
	
	Map<NonTerminal, List<GlobalElement>> elementMap;
	
	//a map from klabel to an element
	Map<String, GlobalElement> klabelMap;
	List<FunctionElement> theFunctionDecls;
	List<GlobalElement> kResultProductions;
	
	public PrinterToIsabelle(Context context) {
		super(context);
		// TODO Auto-generated constructor stub
	}
	
	//a constructor to generate the important information.
	public PrinterToIsabelle(Context context, GlobalElement element) {
		super(context);
		/*
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
		
		generateBuiltinLabels();
		*/
	}
	
	private void generateBuiltinLabels(){
		this.klabelMap.put("'_+Int_", new ThePair("(op +)"));
		this.klabelMap.put("'_*Int_", new ThePair("(op *)"));
		this.klabelMap.put("'_-Int_", new ThePair("(op -)"));
		this.klabelMap.put("'_%Int_", new ThePair("(op mod)"));
		this.klabelMap.put("'_/Int_", new ThePair("(op div)"));
		this.klabelMap.put("'_modInt_", new ThePair("(op mod)"));
		this.klabelMap.put("'_divInt_", new ThePair("(op div)"));
		this.klabelMap.put("'~Int_", new ThePair("-"));

		this.klabelMap.put("'_+Float_", new ThePair("(op +)"));
		this.klabelMap.put("'_*Float_", new ThePair("(op *)"));
		this.klabelMap.put("'_-Float_", new ThePair("(op -)"));
		this.klabelMap.put("'_/Float_", new ThePair("(op div)"));
		this.klabelMap.put("'_^Float_", new ThePair("(op ^)"));
		this.klabelMap.put("'--Float_", new ThePair("-"));
		
		this.klabelMap.put("'_<=Int_", new ThePair("(op \\<le>)"));
		this.klabelMap.put("'_<Int_", new ThePair("(op <)"));
		this.klabelMap.put("'_>Int_", new ThePair("(op >)"));
		this.klabelMap.put("'_>=Int_", new ThePair("(op \\<ge>)"));
		this.klabelMap.put("'_==Int_", new ThePair("(op =)"));
		this.klabelMap.put("'_=/=Int_", new ThePair("(op \\<noteq>)"));

		this.klabelMap.put("'_<=Float_", new ThePair("(op \\<le>)"));
		this.klabelMap.put("'_<Float_", new ThePair("(op <)"));
		this.klabelMap.put("'_>Float_", new ThePair("(op >)"));
		this.klabelMap.put("'_>=Float_", new ThePair("(op \\<ge>)"));
		this.klabelMap.put("'_==Float_", new ThePair("(op =)"));
		this.klabelMap.put("'_=/=Float_", new ThePair("(op \\<noteq>)"));
		this.klabelMap.put("'_==Bool_", new ThePair("(op =)"));
		this.klabelMap.put("'_=/=Bool_", new ThePair("(op \\<noteq>)"));
		this.klabelMap.put("'_==String_", new ThePair("(op =)"));
		this.klabelMap.put("'_=/=String_", new ThePair("(op \\<noteq>)"));
		this.klabelMap.put("'_+String_", new ThePair("stringplus"));
		
		this.klabelMap.put("'notBool_", new ThePair("\\<not>"));
		this.klabelMap.put("'_andBool_", new ThePair("(op \\<and>)"));
		this.klabelMap.put("'_andThenBool_", new ThePair("(op \\<and>)"));
		this.klabelMap.put("'_xorBool_", new ThePair("xor"));
		this.klabelMap.put("'_orBool_", new ThePair("(op \\<or>)"));
		this.klabelMap.put("'_orElseBool_", new ThePair("(op \\<or>)"));
		this.klabelMap.put("'_impliesBool_", new ThePair("(op \\<longrightarrow>)"));
		
		this.klabelMap.put("'lengthString", new ThePair("length"));
		this.klabelMap.put("'substrString", new ThePair("subklist"));
		//wrong implementation
		this.klabelMap.put("'Float2String", new ThePair("length"));
		this.klabelMap.put("'String2Float", new ThePair("length"));
		this.klabelMap.put("'String2Int", new ThePair("length"));
		this.klabelMap.put("'Int2String", new ThePair("string_of_int"));
		
		this.klabelMap.put("'keys(_)", new ThePair("keys"));
		this.klabelMap.put("'_in_", new ThePair("kin"));
		this.klabelMap.put("'size(_)", new ThePair("length"));
		this.klabelMap.put("'values(_)", new ThePair("theValues"));
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
    	/*
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
    	*/
    	return null;
    }
    
    public Void visit(Require req, Void _void) {
    	
    	System.out.println("Require \""+ req.getValue()+"\"");
    	return null;
    }
    
    public Void visit(LiterateDefinitionComment ltc, Void _void) {
    	
    	System.out.println("DefComment \""+ ltc.getValue()+"\"");
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
    	
    	System.out.print("Definition [ ");
        for (int i = 0; i < def.getItems().size(); ++i){
        	if(def.getItems().get(i) instanceof Module){
        		this.visit((Module)(def.getItems().get(i)), _void);
        	}
        	if(def.getItems().get(i) instanceof Require){
        		this.visit((Require)(def.getItems().get(i)), _void);
        	}
        	if(def.getItems().get(i) instanceof LiterateDefinitionComment){
        		this.visit((LiterateDefinitionComment)(def.getItems().get(i)), _void);
        	}
    		if(i != def.getItems().size() - 1){
    			System.out.print(" ; ");
    		}
        }
        
        System.out.println("]");
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
    
    private String correctSort(NonTerminal name){
    	if(name.getSort().equals(Sort.INT))
    		return "int";
    	
    	if(name.getSort().equals(Sort.STRING))
    		return "string";
    	
    	if(name.getSort().equals(Sort.BOOL))
    		return "bool";
    	
    	if(name.getSort().equals(Sort.FLOAT))
    		return "real";
    	
    	return name.toString();
    }
    
    private boolean isBuiltinSort(NonTerminal sort){
    	if(sort.getSort().equals(Sort.ID)
    			|| sort.getSort().equals(Sort.INT)
    			|| sort.getSort().equals(Sort.FLOAT)
    			|| sort.getSort().equals(Sort.BOOL)
    			|| sort.getSort().equals(Sort.BOOL)){
    		return true;
    	}
    	return false;
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
    
    private List<NonTerminal> deleteBuiltinSorts(List<NonTerminal> nextSorts){
    	ArrayList<NonTerminal> newResult = new ArrayList<NonTerminal>();
    	for(int i = 0; i < nextSorts.size(); ++i){
    		if(!isBuiltinSort(nextSorts.get(i))){
    			newResult.add(nextSorts.get(i));
    		}
    	}
    	return (List<NonTerminal>)newResult;
    }
    
    private void printDatatype(){

    	Graph toDeleteGraph = new Graph(((Element)this.theElement).dataDependency);
    	GetNextDataTypeSort nextSorts
    	      = new GetNextDataTypeSort(toDeleteGraph);
    	List<NonTerminal> theNextSort = nextSorts.getNextSort();
    	while(theNextSort != null){
    		theNextSort = deleteBuiltinSorts(theNextSort);
    		for(int outer = 0; outer < theNextSort.size(); ++outer){
    			NonTerminal sort = theNextSort.get(outer);
    			if(outer == 0 && this.elementMap.get(sort).size() == 1
    					&& this.elementMap.get(sort).get(0) instanceof ListElement){
    				System.out.print("type_synonym "+sort+" = ");
    			} else if(outer == 0){
    				System.out.print("datatype "+sort+" = ");
    			} else {
    				System.out.print("and "+sort+" = ");
    			}
            	for(int i = 0; i < this.elementMap.get(sort).size(); ++i){
            		if(this.elementMap.get(sort).get(i) instanceof NormalElement){
            			System.out.print(((NormalElement)this.elementMap
            					.get(sort).get(i)).isabelleLabel+" ");
            			for(int index = 0; index < ((NormalElement)this.elementMap
            					.get(sort).get(i)).arguments.size(); ++index){
            				System.out.print("\""+correctSort((NonTerminal)((NormalElement)this.elementMap
                					.get(sort).get(i)).arguments.get(index))+"\" ");
            			}
            		} else if(this.elementMap.get(sort).get(i) instanceof SubSortElement){
            			System.out.print(((SubSortElement)this.elementMap
            					.get(sort).get(i)).isabelleLabel+" \""
            					+correctSort(((SubSortElement)this.elementMap
                    					.get(sort).get(i)).argument)+"\"");
            			
            		} else if(this.elementMap.get(sort).get(i) instanceof ListElement){
            			System.out.print("\""+correctSort(((ListElement)this.elementMap
                    					.get(sort).get(i)).argument)+" list\"");
            			
            		}
            		if(i != this.elementMap.get(sort).size() - 1){
            			System.out.print(" | ");
            		}
            	}
            	System.out.println();
    		}
    		theNextSort = nextSorts.getNextSort();
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
    	System.out.print("datatype KResult = ");
    	for(int i = 0; i < ((Element)this.theElement).kResultProductions.size(); ++i){
    		if(((Element)this.theElement).kResultProductions.get(i) instanceof NormalElement){
    			System.out.print(((NormalElement)((Element)this.theElement)
    					.kResultProductions.get(i)).isabelleLabel+" ");
    			for(int j = 0; j < ((NormalElement)((Element)this.theElement)
    					.kResultProductions.get(i)).arguments.size(); ++j){
    				System.out.print("\""+correctSort((NonTerminal)((NormalElement)((Element)this.theElement)
        					.kResultProductions.get(i)).arguments.get(j))+"\" ");
    			}
    		} else if(((Element)this.theElement).kResultProductions.get(i) instanceof SubSortElement){
    			System.out.print(((SubSortElement)((Element)this.theElement)
    					.kResultProductions.get(i)).isabelleLabel+" \""
    					+correctSort(((SubSortElement)((Element)this.theElement)
    	    					.kResultProductions.get(i)).argument)+"\"");
    			this.resultMap.put(((SubSortElement)((Element)this.theElement)
    	    					.kResultProductions.get(i)).argument.getSort()
    	    					, ((SubSortElement)((Element)this.theElement)
    	    	    					.kResultProductions.get(i)).isabelleLabel);
    		}
    		if(i != ((Element)this.theElement).kResultProductions.size() - 1){
    			System.out.print(" | ");
    		}
    	}
    	//printout the kresult sort with KDot
    	System.out.println();
    	System.out.println("datatype full_kresult =  Kresult_value \"KResult\" | KDot");
    	System.out.print("datatype KItem = KItemOfKresult \"full_kresult\" | ");
    	ArrayList<Sort> theKeySet = new ArrayList<Sort>();
    	for(int i = 0; i < ((Element)theElement).dataDependency.getVertexList().size(); ++i){
    		if(!this.resultMap.containsKey(((NonTerminal)((Element)theElement)
    				.dataDependency.getVertexList().get(i)).getSort())){
    			theKeySet.add(((NonTerminal)
    					((Element)theElement).dataDependency.getVertexList().get(i)).getSort());
    		}
    	}
    	
    	for(int i = 0; i < theKeySet.size(); ++i){
    		System.out.print("KItemOf"+theKeySet.get(i)+" \""+theKeySet.get(i)+"\"");
    		this.kitemMap.put(theKeySet.get(i), "KItemOf"+theKeySet.get(i));
    		if(i != theKeySet.size() - 1){
    			System.out.print(" | ");
    		}
    	}
    	System.out.println();
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
    /*
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
    */
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
    
    private void printBuiltinItems(){
        System.out.println("fun stringplus where");
        System.out.println("\"stringplus (a::string) (b::string) = concat [a, b]\"");
        System.out.println("fun subklist where");
        System.out.println("\"subklist (a::string) (b::nat) (c::nat) = sublist a {b .. c}\"");
        System.out.println("fun string_of_nat :: \"nat ⇒ string\" where");
        System.out.println("\"string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else"); 
        System.out.println("string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])\"");
        System.out.println("fun string_of_int :: \"int ⇒ string\" where");
        System.out.println("\"string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else");
        System.out.println("string_of_nat (nat i))\"");
        System.out.println("type_synonym K = \"kitem list\"");
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
        System.out.println("fun kin where");
        System.out.println("\"kin a b = (a ∈ (kSetToSet b))\"");
    }

    public Void visit(Import imp, Void _void) {
    	System.out.println("Import ( ModId \""+imp.getName()+"\")");
    	return null;
    }
    
    public Void visit(LiterateModuleComment item, Void _void) {
    	System.out.println("ModComment \""+item.getValue()+"\"");
    	return null;
    }
    
    
    public Void visit(Attributes item, Void _void){
    	System.out.print("[");
    	ArrayList<Attribute<?>> valueList = new ArrayList<Attribute<?>>(item.values());
    	for(int i = 0; i < valueList.size(); ++i){
    		if(valueList.get(i).equals(Attribute.ANYWHERE)){
    			System.out.println("Anywhere");
    		} else if(valueList.get(i).equals(Attribute.BRACKET)){
    			System.out.println("Bracket");
    		} else if(valueList.get(i).equals(Attribute.FUNCTION)){
    			System.out.println("Function");
    		} else if(valueList.get(i).equals(Attribute.MACRO)){
    			System.out.println("Macro");
    		} else if (valueList.get(i).getKey().equals(Attribute.SEQSTRICT_KEY)){
    			System.out.println("Seqstrict");
    		} else if (valueList.get(i).getKey().equals("left")){
    			System.out.println("Leftassoc");
    		} else if (valueList.get(i).getKey().equals("right")){
    			System.out.println("Rightassoc");
    		} else if (valueList.get(i).getKey().equals("onlyLabel")){
    			System.out.println("OnlyLabel");
    			
    		} else if (valueList.get(i).getKey().equals("cool")){
    			System.out.println("CoolRule");
    		} else if (valueList.get(i).getKey().equals("Heat")){
    			System.out.println("HeatRule");
    		} else if (valueList.get(i).getKey().equals("klabel")){
    			System.out.print("Klabel \"");
    			System.out.print(valueList.get(i).getValue());
    			System.out.println("\"");
    		} else if (valueList.get(i).getKey().equals("strict")){
    			System.out.print("Strict [");
    			System.out.print(((String)valueList.get(i).getValue()).replace(',',';'));
    			System.out.println("]");
    		} else {
    			System.out.print("Attribute (\""+valueList.get(i).getKey()+"\", ");
    			System.out.println("\""+valueList.get(i).getValue() + "\")");
    		}
    		
        	if(i != valueList.size() - 1){
    			System.out.print(" ; ");
    		}
    	}
    	System.out.println("]");
    	return null;
    }
    
    public Void visit(UserList item, Void _void) {
    	
    	if(item.getListType().equals(UserList.ZERO_OR_MORE)){
    		System.out.println("UserList (SortId \""+item.getSort().getName()
        			+"\" , \""+item.getSeparator()+"\" , NormalList)");
    	} else {
    		System.out.println("UserList (SortId \""+item.getSort().getName()
        			+"\" , \""+item.getSeparator()+"\" , NeList)");

    	}
    	return null;
    }
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Production, java.lang.Object)
     * 
     */
    public Void visit(Production item, Void _void) {
    	
    	if(item.isListDecl()){
    		this.visit((UserList) item.getItems().get(0), _void);
    	} else if(item.isSyntacticSubsort()){
    		if(item.isSubsort()){
    			System.out.print("SubsortRelation (SortId \"" + ((NonTerminal)item.getItems().get(0)).getName() +"\", ");
    			this.visit(item.getAttributes(), _void);
    		    System.out.println(")");
    		    
    		} else {
    			System.out.print("Normal ([ "+item.getKLabel() +"; Terminal \"(\" ; NonTerminal (SortId \""
    		               + ((NonTerminal)item.getItems().get(0)).getName() + "\") ; Terminal \")\" ], ");
    			this.visit(item.getAttributes(), _void);
    		    System.out.println(")");
    		    
    		}
    	} else if (item.isLexical()){
    		System.out.print("LexToken (\""+ ((Lexical)item.getItems().get(0)).getLexicalRule() + "\", ");
			this.visit(item.getAttributes(), _void);
		    System.out.println(")");
		    
    	} else if (item.isTerminal()){
    		if(item.isConstant()){
    			System.out.print("Constant (SortId \""+ item.getSort().getName() + "\", Terminal \""
    		               + ((Terminal)item.getItems().get(0)).getTerminal() +"\", ");
    			this.visit(item.getAttributes(), _void);
    		   	System.out.println(")");
    		   	
    		}
    		else {
    			System.out.print("Normal ([Terminal \"" + ((Terminal)item.getItems().get(0)).getTerminal() +"\"], ");
    			this.visit(item.getAttributes(), _void);
    		   	System.out.println(")");

    		}
    	} else if(item.isBracket()){
    		System.out.print("Bracket ([");
    		for(int i = 0; i < item.getItems().size(); ++i){
    			if(item.getItems().get(i) instanceof Terminal){
    				System.out.println("Terminal \""+((Terminal)item.getItems().get(i)).getTerminal() + "\"");
    			} else if(item.getItems().get(i) instanceof NonTerminal){
    				System.out.println("NonTerminal (SortId \""+((NonTerminal)item.getItems().get(i)).getName() + "\")");
    			}
    			
            	if(i != item.getItems().size() - 1){
        			System.out.print(" ; ");
        		}
    		}
    		System.out.print("], ");
			this.visit(item.getAttributes(), _void);
		   	System.out.println(")");

    	} else {
    		System.out.print("Normal ([");
    		for(int i = 0; i < item.getItems().size(); ++i){
    			if(item.getItems().get(i) instanceof Terminal){
    				System.out.println("Terminal \""+((Terminal)item.getItems().get(i)).getTerminal() + "\"");
    			} else if(item.getItems().get(i) instanceof NonTerminal){
    				System.out.println("NonTerminal (SortId \""+((NonTerminal)item.getItems().get(i)).getName() + "\")");
    			}
    			
            	if(i != item.getItems().size() - 1){
        			System.out.print(" ; ");
        		}
    		}
    		System.out.print("], ");
			this.visit(item.getAttributes(), _void);
		   	System.out.println(")");

    		
    	}
        
    	return null;
    }

    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.PriorityBlock, java.lang.Object)
     * in printout the priority block, it is a ocaml structure with two fields
     * the first field is a string to represent assoc, and the second one is a list of productions.
     */
    public Void visit(PriorityBlock item, Void _void) {
    	System.out.print("PriorityBlock ( \"" +item.getAssoc()+"\", [");
        for (int i = 0; i < item.getProductions().size(); ++i){
        	this.visit((Production)item.getProductions().get(i), _void);
    		if(i != item.getProductions().size() - 1){
    			System.out.print(" ; ");
    		}
        }
    	System.out.println("])");
    	
    	return null;
    }
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Syntax, java.lang.Object)
     * print out a list of priority blocks and the list is ordered list so that the formal
     * element has higher priority in a grammar.
     */
    public Void visit(Syntax item, Void _void) {
    	System.out.print("Syntax ( SortId \""+item.getDeclaredSort().getName()+"\", [");
        for (int i = 0; i < item.getPriorityBlocks().size(); ++i){
        	this.visit((PriorityBlock)item.getPriorityBlocks().get(i), _void);
    		if(i != item.getPriorityBlocks().size() - 1){
    			System.out.print(" ; ");
    		}
        }
    	System.out.println("])");
    	return null;
    }
    
    public Void visit(Configuration item, Void _void) {
    	
    	System.out.print("Configuration ");
    	this.visit(item.getBody(), _void);
    	return null;
    }
    
    public Void visit(Sentence item, Void _void) {
    	
    	if(item instanceof Configuration){
    		this.visit((Configuration)item, _void);
    	}
    	return null;
    }
    
    /*
     * The visitor module function will
     * print out the datatypes by using printDatatype function
     * , printKItem function and printCellDatatype function.
     * then, it will genereate only one inductive rules for all the non-function
     * rules in K.
     */
    public Void visit(Module mod, Void _void) {
    	System.out.print("Module ( ModId \""+mod.getName()+"\", [ ");
        for (int i = 0; i < mod.getItems().size(); ++i){
        	
        	if(mod.getItems().get(i) instanceof Import){
        		this.visit((Import)(mod.getItems().get(i)), _void);
        	} else if(mod.getItems().get(i) instanceof LiterateModuleComment){
        		this.visit((LiterateModuleComment)(mod.getItems().get(i)), _void);
        	} else if(mod.getItems().get(i) instanceof Syntax){
        		this.visit((Syntax)(mod.getItems().get(i)), _void);
        	} else if(mod.getItems().get(i) instanceof Sentence){
        		this.visit((Sentence)(mod.getItems().get(i)), _void);
        	}
        	
    		if(i != mod.getItems().size() - 1){
    			System.out.print(" ; ");
    		}
        }
    	System.out.println(" ])");
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
    /*
    public Void visit(Rewrite rewrite, Void _void) {
        if(! (rewrite.getLeft() instanceof KSequence)
        		&& !(rewrite.getRight() instanceof KSequence)
        		&& !(rewrite.getRight() instanceof Bag)
        		&& !(rewrite.getRight() instanceof Bag)){
        	if(this.resultMap.containsKey(rewrite.getRight().getSort())){
        		System.out.print("Final ");
        	}else {
        		System.out.print("Direct ");
        	}
        	
        	this.visit(rewrite.getLeft(), _void);
        	System.out.print(" ");
        	if(this.resultMap.containsKey(rewrite.getRight().getSort())){
        		System.out.println("(Kresult_value ");
        		System.out.print(this.resultMap.get(rewrite.getRight().getSort()));
        	} else{
        		System.out.println("(");
        		System.out.print(this.kitemMap.get(rewrite.getRight().getSort()));
        	}
        	this.visit(rewrite.getRight(), _void);
        	System.out.println(")");
        }

    	return null;
    }
    */
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
    	
    	if(rule.getRequires() != null){
    		this.visit(rule.getRequires(), _void);
    		System.out.print(" \\<Longrightarrow> ");
    	}
    	if(rule.getBody() instanceof Rewrite){
    		this.visit(rule.getBody(), _void);
    	}
    	System.out.println("\"");
    	/*
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
        */
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
    	
    	ArrayList<Entry<String, String>> entryList
    	               = new ArrayList<Entry<String, String>>();
        String attributes = "[";
        for (int i = 0; i < entryList.size(); ++i){
        	attributes += "(\"" + entryList.get(i).getKey() + "\", \""
                                 + entryList.get(i).getValue() + "\")";
            if(i != entryList.size() - 1){
            	attributes += " ; ";
            }
        }
        attributes += "]";
        
        System.out.print("Cell (CellName \"" + cell.getLabel() + "\", "+attributes+", ");
        this.visit(cell.getContents(), _void);
        System.out.println(")");
        return null;
    }
    
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.Bag, java.lang.Object)
     * the bag visitor is a list of cells.
     * We just visit it by call cell visitor function in each child of the Bag
     */
    public Void visit(Bag bag, Void _void) {
    	
    	System.out.print("Bag [");
        for (int i = 0; i < bag.getContents().size(); ++i) {
            this.visit((Term)(bag.getContents().get(i)), _void);
            if(i != bag.getContents().size() - 1){
            	System.out.print(" ; ");
            }
        }
    	System.out.println("]");
        return null;
    }
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.KList, java.lang.Object)
     * KList visitor is a list of KSequence.
     * In K, we have
     * KSequence (which is the same as K) = KItem list
     * KItem = klabel(KList)
     * KList = KSequence list
     * 
     * However, the K cell usually start at the level of K
     * 
     * We need to call visitor of KSequence on each child of the klist.
     */
    /*
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
    */
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.KApp, java.lang.Object)
     * KApp visitor is equal to KItem.
     * Its form is like 
     * KApp(KItem) = klabel(KList)
     * 
     * this visitor function will call
     * the KLabelConstant visitor function for the klabel
     * and the Klist visitor function for the kList
     * 
     * However, there are special cases.
     * 
     * a KApp could be a token, In K, token is viewed as KApp
     * 
     * for example, when we see the rule
     * rule A => 1
     * the 1 is really a token (interger token), then it is acutally a KApp
     * in K, and it will be print out in the internal like 1(.KList)
     * 
     * However, we don't want that in Isabelle. We need to print out 1 as 1
     * in Isabelle. so we need to avoid printing out the KList part when we found that
     * the klabel is actually a token in KAPP
     * In this case, the KAPP will use token visitor functions for its klabel part.
     */
    /*
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
    */
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.KLabelConstant, java.lang.Object)
     * for the klabel in a KApp = klabel(KList) structure.
     */
    public Void visit(KLabelConstant kLabelConstant, Void _void) {
        System.out.print(this.generateName(kLabelConstant.getLabel()));
        return null;
    }
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.KSequence, java.lang.Object)
     * KSequence is a list of KApp (or KItem), we need to visit the each child of the KSequence
     * by KApp visitor function.
     * The problem is that in K, we can write something like:
     * 
     * rule A:AExp => 1
     * rule B:BExp => 2
     * 
     * where A and B are two different sorts and 1 and 2 belong to interger sort which is
     * different from AExp and BExp.
     * 
     * In Isabelle, we need to have unique sort relation in LHS and RHS of each rule.
     * 
     * Hence, we need to normalize the sort, for the rules above, we need to print out like
     * 
     * rule (AExpKItem A)#[] => (IntKItem 1)#[]
     * rule (BExpKItem B)#[] => (IntKItem 2)#[]
     * 
     * where the AExpKItem, BExpKItem and IntKItem are all constructors and the meaning of them
     * is to translate the AExp, BExp and Int terms into KItem terms.
     * 
     * In addition, since most LHS and RHS is written in the KSequence level, we
     * must also make the RHS and LHS of Isabelle translation to be in the KSequence level
     * by adding #[] in the end.
     */
    /*
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
    */
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.ListBuiltin, java.lang.Object)
     * belows are the buildtins and tokens functions.
     
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
    */
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
    
    /*
     * (non-Javadoc)
     * @see org.kframework.kil.AbstractVisitor#visit(org.kframework.kil.TermCons, java.lang.Object)
     * TermCons are actually similar to KApp. It just have a strange structure.
     * Read the things in KApp to know the implementation detail.
     * People in K group to store something in TermCons because
     * they want to save their parsing time.
     * The store structure of termcons can be divided into two different categories.
     * If the termCons is a list declration type such as A,B,C,its store structure
     * is different from if the termCons has normal type.
     * Read the visit function carefully to know the detail.
     * However, we need to know that the concepts of the termCons have no difference with
     * the concepts of KApp.
     */
    /*
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
            
            if(termCons.getSort().equals(Sort.MAP)) {
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
            	System.out.print("("+klabelMap
            			.get(this.generateKLabel(production)).getIsabelleLabel());
                for(int i = 0; i < termList.size(); ++i){
                	System.out.print(" ");
                	this.visit(termList.get(i), _void);
                }
                System.out.print(")");
            }
        }
        return null;
    }
    */
}
