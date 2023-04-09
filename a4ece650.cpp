#include <iostream>
#include <string>
#include <regex>
#include <vector>
#include <unordered_map>
#include <list>
#include <queue>
#include <utility>
#include <climits>
#include <bits/stdc++.h>
#include <pthread.h>
#include <time.h>
#include <string>
#include <minisat/core/Solver.h>
#include <minisat/core/SolverTypes.h>
#define MAX 100000

#define INFINITY 200000
using namespace std;
using namespace Minisat;

class checkInput
{
public:
    bool edgeValidation(const std::vector<std::pair<int, int>> &ed, int num_vertices) const
    {
        return std::all_of(ed.begin(), ed.end(), [num_vertices](const std::pair<int, int> &ed1)
                           {
                               return ed1.first >= 0 && ed1.first <= num_vertices && ed1.second >= 0 && ed1.second <= num_vertices;
                               // && ed1.first != ed1.second;
                           });
    }
};

vector<pair<int, int>> edge_Parser(string st)
{
    pair<int, int> e;
    vector<pair<int, int>> edges_Parsed;
    vector<pair<int, int>> edges1;
    regex re("-?[0-9]+");
    auto m = sregex_iterator(st.begin(), st.end(), re);
    auto n = sregex_iterator();
    auto p = sregex_iterator();
    for (std::sregex_iterator i = m; i != n; ++i)
    {
        smatch s1 = *i;
        smatch s2 = *++i;
        e.first = stoi(s1.str()) - 1;
        e.second = stoi(s2.str()) - 1;
        edges_Parsed.push_back(e);
        // cout << e.first << " " << e.second<<endl;
    }

    return edges_Parsed;
}

class make_Graph
{

    int v;
    int flag = 0;
    
    vector<std::pair<int,int>> route;

    public:
    
    make_Graph(int w)
    {
        this->v = w;
        // int v1 = 0;
        

    }

    // void reset()
    // {
    //     route.clear();
    //     v = 0;
    // }

    void add_ToAdj(vector< std::pair<int,int> > e){
        this->route = e;
    }

    int get_vtx(){
        return v;
    }

    vector<pair<int,int>> get_route(){
        return route;
    }

    
};

pthread_t t1, t2, t3, t4, t5, t6, IO_thread;
make_Graph g(1);
vector<int> result_cnf, result_3cnf, result_approxVC1, result_approxVC2, result_red_approxVC1, result_red_approxVC2;
    
    Minisat::Var generateUniqueIndexForBoolVariable(int rowAdj, int currPositions, int totalPositions){
        int boolVar = currPositions +rowAdj*totalPositions;
        return (boolVar);
    } 

    void case1(Minisat::Solver& minisat, int totalPositions, int v) {
        int i = 0;
        int p = 0;
        while (i < totalPositions) {
            Minisat::vec<Minisat::Lit> c;
            int j = 0;
            int q = 0;
            for (j = 0; j < v; j++) {
                c.push(Minisat::mkLit(generateUniqueIndexForBoolVariable(j,i,totalPositions)));
            }
            minisat.addClause(c);
            i++;
        }
    }

    void case2(Minisat::Solver& minisat, int totalPositions, int v){
        int i = 0;
        int p = 0;
        while (i < v) {
            int j = 0;
            int q = 0;
            while (j < totalPositions) {
                int m = 0;
                int n = 0;
                while (m < j) {
                    minisat.addClause(~Minisat::mkLit(generateUniqueIndexForBoolVariable(i, m, totalPositions)),
                                    ~Minisat::mkLit(generateUniqueIndexForBoolVariable(i, j, totalPositions)));
                    m++;
                }
                j++;
            }
            i++;
        }

    }   

    void case3(Minisat::Solver& minisat, int totalPositions, int v){
        int i = 0;
        int p = 0;
        while(i < totalPositions){
            int j = 0;
            int q = 0;
            while(j < v){
                int m = 0;
                int n = 0;
                while(m < j){
                    minisat.addClause( ~Minisat::mkLit(generateUniqueIndexForBoolVariable(m,i,totalPositions)), ~Minisat::mkLit(generateUniqueIndexForBoolVariable(j,i,totalPositions)));
                    m++;
                }
                j++;
            }
            i++;
        }
    }  
    void case4(Minisat::Solver& minisat, int totalPositions, int v, vector< pair<int,int> > route){
        int i =0;
        for (auto& p : route){
            Minisat::vec<Minisat::Lit> lit;
            int q = 0;
            int j = q;
            while (j < totalPositions) {
                lit.push(Minisat::mkLit(generateUniqueIndexForBoolVariable(p.first, j, totalPositions)));
                lit.push(Minisat::mkLit(generateUniqueIndexForBoolVariable(p.second, j, totalPositions)));
                j++;
            }

            minisat.addClause(lit);
        }
    }

    

    bool checkSatisfiability(Minisat::Solver& minisat, int totalPositions, int v, vector<pair<int,int>> route){
        int rowAdj =0;
        for( rowAdj =0; rowAdj<v; rowAdj++){
            for(int currPositions=0;currPositions<totalPositions;currPositions++){
                minisat.newVar();
            }
        }
         
        case1(minisat, totalPositions, v);
        case2(minisat, totalPositions, v);
        case3(minisat, totalPositions, v);
        case4(minisat, totalPositions, v, route);
        return minisat.solve();
    }  

    vector<int> getRoute(Minisat::Solver& minisat, int currVtx, int v){
        vector<int> p;
        for (int rowAdj = 0; rowAdj < v; rowAdj++) {
            int currPositions = 0;
            while (currPositions < currVtx) {
                if (minisat.modelValue(generateUniqueIndexForBoolVariable(rowAdj, currPositions, currVtx)) == Minisat::toLbool(0)) {
                    p.push_back(rowAdj);
                }
                currPositions++;
            }
        }
        sort(p.begin(), p.end());
        return p;
    }

// Function to implement CNF-SAT-VC
vector<int> cnf_sat_vc(make_Graph g1)
{
    int v = g1.get_vtx();
    vector< pair<int,int> > route = g1.get_route();

    if (route.empty()) {
        // cerr << endl;
        vector<int> {};
        // return;
    }

    // int ip[v];
    //int op[v] = {-1};
      std::vector<int> op(v, -1); 
    int currVtx = 0;
    vector<int> finalRoute[v];
    int low = 0, hi = v, mid;

    while (low <= hi) {
            mid = (hi+low)/2;
            Minisat::Solver minisat;
            op[mid] = checkSatisfiability(minisat,mid, v, route);
            if(op[mid]) {
                finalRoute[mid] = getRoute(minisat, mid,v);
            }

            if(op[mid] ==1 && op[mid-1] ==0 && mid!=0) {
                return (finalRoute[mid]);
            }

            if(op[mid]== 0 && op[mid+1]== 1 && mid!= v) {
                return (finalRoute[mid+1]);
            }

            if (op[mid]) {
                hi = mid - 1;
            }
            else {
                low = mid + 1;
            }
        }
        return vector<int> {};

}
   vector<int> pair_to_int_vector(vector<pair<int, int>> pairs) {
    vector<int> result;
    for (auto p : pairs) {
        result.push_back(p.first);
        result.push_back(p.second);
    }
    return result;
}

vector<int> SATSOLVER(int Vertexes, int no_covers, vector<int> edges) {

    // Create a MiniSat solver instance
    Solver solve;
    //cout<<"In vertex cover"<<endl;

    // Adding these conditions :

   // creating Literals 
    vector<vector<Lit>> matrix(Vertexes);
    for (int i = 0; i < Vertexes; i++) {
        for (int j = 0; j < no_covers; j++) {
            matrix[i].push_back(mkLit(solve.newVar()));
        }
    }
        //At least one vertex is the ith vertex in the vertex cover:
for (int j = 0; j < no_covers; j++) 
{
    vec<Lit> clause;
    for (int i = 0; i < Vertexes; i++) 
    {
        clause.push(matrix[i][j]);
    }

    int size_clause = clause.size();
    vector<vec<Lit>> clauses;
    if(size_clause > 3){

        vec<Lit> new_clause;
        Lit lit1 = clause[0],lit2 = clause[1];
        new_clause.push(lit1);
        new_clause.push(lit2);

        Var new_var = solve.newVar();
        new_clause.push(mkLit(new_var));
        solve.addClause(new_clause);

        for(int i = 2; i < size_clause - 2; i++){
            vec<Lit> more_new_clause;
            more_new_clause.push(~mkLit(new_var));
            if(i < size_clause) {
                more_new_clause.push(clause[i]);
            }
            Var new_var2 = solve.newVar();
            more_new_clause.push(mkLit(new_var2));
            // clauses.push_back(more_new_clause);
            solve.addClause(more_new_clause);
            new_var = new_var2;
        }

        vec<Lit> final_clause;
        final_clause.push(~mkLit(new_var));
        final_clause.push(clause[size_clause - 2]);
        final_clause.push(clause[size_clause - 1]);
        // clauses.push_back(final_clause);
        solve.addClause(final_clause);
    }

    // for(int i = 0 ; i < clauses.size();i++)   solve.addClause(clauses[i]);
    else solve.addClause(clause);
}



     //No one vertex can appear twice in a vertex cover

 
for (int j = 0; j < no_covers - 1; j++) {
    for (int k = j + 1; k < no_covers; k++) {
        vec<Lit> clause;
        for (int i = 0; i < Vertexes; i++) {
            clause.push(matrix[i][j]);
            clause.push(matrix[i][k]);
        }

        int l = 0, r = Vertexes - 1;
        while (l <= r) {
            int mid = (l + r) / 2;
            bool found_j = sign(matrix[mid][j]);
            bool found_k = sign(matrix[mid][k]);
            if (!found_j && !found_k) {
                l = mid + 1;
            } else if (found_j && found_k) {
                r = mid - 1;
            } else {
                break;
            }
        }

        for (int m = l; m <= r; m++) {
            solve.addClause(~matrix[m][j], ~matrix[m][k]);
        }
    }
}


    //No more than one vertex appears in the mth position of the vertex cover

    for (int j = 0; j < no_covers; j++) {
        for (int i = 0; i < Vertexes - 1; i++) {
            for (int k = i + 1; k < Vertexes; k++) {
                solve.addClause(~matrix[i][j], ~matrix[k][j]);
            }
        }
    }
    //Every edge is incident to at least one vertex in the vertex cover.

    for (int i = 0; i < edges.size(); i += 2) {
        int x = edges[i];
        int y = edges[i+1];
        vec<Lit> clause;
        for (int j = 0; j < no_covers; j++) {
            clause.push(matrix[x][j]);
            clause.push(matrix[y][j]);
        }

    int size_clause = clause.size();
   
    if(size_clause > 3){

        

        vec<Lit> new_clause;
        Lit lit1 = clause[0],lit2 = clause[1];
        new_clause.push(lit1);
        new_clause.push(lit2);

        Var new_var = solve.newVar();
        new_clause.push(mkLit(new_var));
        solve.addClause(new_clause);

        for(int i = 2; i < size_clause - 2; i++){
            vec<Lit> more_new_clause;
            more_new_clause.push(~mkLit(new_var));
            if(i < size_clause) {
                more_new_clause.push(clause[i]);
            }
            Var new_var2 = solve.newVar();
            more_new_clause.push(mkLit(new_var2));
            solve.addClause(more_new_clause);
            new_var = new_var2;
        }

        vec<Lit> final_clause;
        final_clause.push(~mkLit(new_var));
        final_clause.push(clause[size_clause - 2]);
        final_clause.push(clause[size_clause - 1]);
        solve.addClause(final_clause);
    }

        else solve.addClause(clause);
    }

    // Solve the problem using MiniSat
    bool sat = solve.solve();

    if (sat== true) {
        // Extract the vertices that are included in the cover
        vector<int> result;
        for (int i = 0; i < Vertexes; i++) {
            for (int j = 0; j < no_covers; j++) {
                if (toInt(solve.modelValue(matrix[i][j])) == 0) {
                    result.push_back(i);
                    break;
                }
            }
        }
       // cout<<"result calculated"<<endl;
        return result;
    } else {
        // The problem is unsatisfiable
        return {-1};
    }
}








// Function to implement CNF-3-SAT-VC
vector<int> cnf_3_sat_vc(make_Graph g1)
{
    int V = g1.get_vtx();
    vector< pair<int,int> > route = g1.get_route();
    int start = 1;
int end = V;
vector<int> answer;
vector<int> answer_final;
//vector<int> intVertices{ 0,4,4,1,0,3,3,4,3,2,1,3 };
vector<int> temp = {-1};
vector<int> Vertices=  pair_to_int_vector(route);
for (int i = start; i <= end; i++) {
    answer = SATSOLVER(V, i , Vertices);
    //bool check = std::equal(result.begin(), result.end(), tmp.begin());
    bool cond= (answer == temp);
    if ( cond == false) {
        answer_final.clear();
        answer_final = answer;
        break;
    } else {
        answer_final = answer;
    }
}
sort(answer_final.begin(), answer_final.end(), [](int a, int b) { return a < b;});
    return vector<int> {};
}

// Function to implement APPROX-VC-1
vector<int> approx_vc_1(make_Graph g1)
{   int V = g1.get_vtx();
    vector< pair<int,int> > route = g1.get_route();

    vector<int> result;

    while (!route.empty()) {
        vector<int> cnt(V, 0);
        for (auto edge : route) {
            cnt[edge.first]++;
            cnt[edge.second]++;
        }

        int max_degree_vertex = std::max_element(cnt.begin(), cnt.end()) - cnt.begin();
        result.push_back(max_degree_vertex);

        vector<pair<int, int>> new_route;
        for (auto edge : route) {
            if (edge.first == max_degree_vertex || edge.second == max_degree_vertex) {
                continue;
            }
            new_route.push_back(edge);
        }
        route = new_route;
    }

    return result;
}

// Function to implement APPROX-VC-2

vector<int> approx_vc_2(make_Graph g1)
{
    int V = g1.get_vtx();
    vector< pair<int,int> > route = g1.get_route();

    vector<int> result;
    vector< pair<int,int> > edges = route;
    
    while (!edges.empty()) {
        int u = edges[0].first;
        int v = edges[0].second;
        
        result.push_back(u);
        result.push_back(v);
        
        vector< pair<int,int> > new_edges;
        
        for (const auto& edge : edges) {
            if (edge.first != u && edge.second != u && edge.first != v && edge.second != v) {
                new_edges.push_back(edge);
            }
        }
        
        edges = new_edges;
    }
    
    return result;
}



// Function to implement REFINED-APPROX-VC-1
vector<int> refined_approx_vc_1(make_Graph g1)
{
    int V = g1.get_vtx();
    vector<pair<int, int>> route = g1.get_route();

    vector<int> result;

    while (!route.empty()) {
        vector<int> cnt(V, 0);
        for (auto edge : route) {
            cnt[edge.first]++;
            cnt[edge.second]++;
        }

        int max_degree_vertex = std::max_element(cnt.begin(), cnt.end()) - cnt.begin();
        result.push_back(max_degree_vertex);

        vector<pair<int, int>> new_route;
        for (auto edge : route) {
            if (edge.first == max_degree_vertex || edge.second == max_degree_vertex) {
                continue;
            }
            new_route.push_back(edge);
        }
        route = new_route;
    }

    // Go through the set of vertices and remove unnecessary ones
    for (auto v : result) {
        // Compute C - {v} to see if v is necessary
        vector<pair<int, int>> new_route;
        for (auto edge : route) {
            if (edge.first == v || edge.second == v) {
                continue;
            }
            new_route.push_back(edge);
        }

        // If C - {v} is not a vertex cover, keep v in the result
        bool is_vertex_cover = true;
        for (auto edge : g1.get_route()) {
            if (edge.first == v || edge.second == v) {
                continue;
            }
            if (find(new_route.begin(), new_route.end(), edge) == new_route.end()) {
                is_vertex_cover = false;
                break;
            }
        }

        if (!is_vertex_cover) {
            route = new_route;
        }
    }

    return result;
}

bool is_vertex_cover(make_Graph g1, vector<int> cover)
{
    for (const auto& edge : g1.get_route()) {
        if (find(cover.begin(), cover.end(), edge.first) == cover.end() &&
            find(cover.begin(), cover.end(), edge.second) == cover.end()) {
            // If neither endpoint of the edge is in the cover, it is not a vertex cover
            return false;
        }
    }
    
    return true;
}

// Function to implement REFINED-APPROX-VC-2
vector<int> refined_approx_vc_2(make_Graph g1)
{
    int V = g1.get_vtx();
    vector< pair<int,int> > route = g1.get_route();

    vector<int> result;
    vector< pair<int,int> > edges = route;
    
    while (!edges.empty()) {
        int u = edges[0].first;
        int v = edges[0].second;
        
        result.push_back(u);
        result.push_back(v);
        
        vector< pair<int,int> > new_edges;
        
        for (const auto& edge : edges) {
            if (edge.first != u && edge.second != u && edge.first != v && edge.second != v) {
                new_edges.push_back(edge);
            }
        }
        
        edges = new_edges;
    }

    // Removing unnecessary vertices
    vector<int> vertex_cover(result);
    for (const auto& vertex : result) {
        vertex_cover.erase(remove(vertex_cover.begin(), vertex_cover.end(), vertex), vertex_cover.end());
        if (is_vertex_cover(g1, vertex_cover)) {
            // If removing the vertex leaves a vertex cover, it is not needed
            continue;
        }
        else {
            // If removing the vertex does not leave a vertex cover, add it back
            vertex_cover.push_back(vertex);
        }
    }
    
    return vertex_cover;
}



void print_value(string n, vector<int> result) {
        // cout << "ddddddddddddddddddddddddddccccccccccccajfhs" <<endl;
    // int v = g1.get_vtx();
    // vector< pair<int,int> > route = g1.get_route();
    cout << n << ": ";
    if (result.empty()) {
        cout << endl;
        return;
    }
       

    sort(result.begin(), result.end());
    for (int i = 0; i < (int)result.size(); i++) {
        // cout << "ajfhs" <<endl;
        int j = i + 1;
        if (j == (int)result.size()) {
            cout << (result[i] + 1);
        } else {
            cout << (result[i] + 1) << ",";
        }
    }
    result.clear();
    // cout << "V: "<<v<<endl;
    cout << endl;
}


// Handler function for CNF-SAT-VC
void *cnf_sat_vc_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
    result_cnf = cnf_sat_vc(g);
    
    print_value("CNF-SAT-VC",result_cnf);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;
    return NULL;
}




// Handler function for CNF-3-SAT-VC
void *cnf_3_sat_vc_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
    result_cnf = cnf_sat_vc(g);
    print_value("CNF-3-SAT-VC",result_cnf);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;



     result_3cnf = cnf_3_sat_vc(g);
    
    return NULL;
}






// Handler function for APPROX-VC-1
void *approx_vc_1_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
     result_approxVC1 = approx_vc_1(g);
     print_value("APPROX-VC-1" ,result_approxVC1);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;
    return NULL;
}

// Handler function for APPROX-VC-2
void *approx_vc_2_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
    result_approxVC2 = approx_vc_2(g);
    print_value("APPROX-VC-2" ,result_approxVC2);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;

    return NULL;
}

// Handler function for REFINED-APPROX-VC-1
void *refined_approx_vc_1_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
    result_red_approxVC1 = refined_approx_vc_1(g);
    print_value("REFINED-APPROX-VC-1" ,result_red_approxVC1);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;
    return NULL;
}

// Handler function for REFINED-APPROX-VC-2
void *refined_approx_vc_2_handler(void *arg)
{   clock_t start, finish;
	double duration;

	start = clock();
    result_red_approxVC2 = refined_approx_vc_2(g);
    print_value("REFINED-APPROX-VC-2" ,result_red_approxVC2);
    finish = clock();

	duration = (double)(finish - start)/CLOCKS_PER_SEC;
	cout << "the duration time is: " << duration << endl;
    // cout << "REFINED-APPROX-VC-2: " << result_red_approxVC2 << endl;
    return NULL;
}

// Handler function for input/output
void *IOHandler_thread(void *args)
{
    string input;
    getline(cin, input);

    char cmnd = input[0];
    string rest = input.substr(2);

    int vtx = 0;
    string edges;

    while (true)
    {
        if (cmnd == 'V')
        {
            vtx = stoi(rest);
            if (vtx < 0)
            {
                int cmd = 0;
                cerr << "Error: No. of vertex should be more than 0" << endl;
                continue;
            }
            else
            {
                // delete g;
                g = make_Graph(vtx);
            }
        }
        else if (cmnd == 'E')
        {
            edges = rest;
            vector<pair<int, int>> line = edge_Parser(edges);
            checkInput checker;
            // cout << vtx <<endl; //5
            if (!checker.edgeValidation(line, vtx))
            {
                cerr << "Error: Invalid vertex entered, the vertices should be between 1 and " << vtx << endl;
                continue;
            }
            else
            {
                g.add_ToAdj(line);
                pthread_create(&t1, NULL, &cnf_sat_vc_handler, NULL);
                // pthread_join(t1, NULL);
                struct timespec tsp;
                int t;
                if (clock_gettime(CLOCK_REALTIME, &tsp) == -1) {
                    cout<<"Error: in getting current time";
                }
                tsp.tv_sec += 120;

                t = pthread_timedjoin_np(t1, NULL, &tsp);
                if (t != 0) {
                    cout<<"CNF-SAT-VC: timeout"<<endl;
                }
                pthread_create(&t2, NULL, &cnf_3_sat_vc_handler, NULL);
                // pthread_join(t2, NULL);
                int s;
                if (clock_gettime(CLOCK_REALTIME, &tsp) == -1) {
                    cout<<"Error: in getting current time";
                }
                tsp.tv_sec += 120;

                s = pthread_timedjoin_np(t2, NULL, &tsp);
                if (s != 0) {
                    cout<<"CNF-3-SAT-VC: timeout"<<endl;
                }
                pthread_create(&t3, NULL, &approx_vc_1_handler, NULL);
                pthread_join(t3, NULL);
                pthread_create(&t4, NULL, &approx_vc_2_handler, NULL);
                pthread_join(t4, NULL);
                pthread_create(&t5, NULL, &refined_approx_vc_1_handler, NULL);
                pthread_join(t5, NULL);
                pthread_create(&t6, NULL, &refined_approx_vc_2_handler, NULL);
                pthread_join(t6, NULL);
            }
        }
        if (!getline(cin, input)) break;

        cmnd = input[0];
        rest = input.substr(2);
    }

    return NULL;
}






int main()
{
    int io_thread;
    io_thread = pthread_create(&IO_thread, NULL, &IOHandler_thread, NULL);
    if (io_thread)
    {
        cerr << "Error: thread not created" << endl;
    }
    pthread_join(IO_thread, NULL);
    // cout<<"I am here";
    pthread_exit(NULL);
    return 0;
}   