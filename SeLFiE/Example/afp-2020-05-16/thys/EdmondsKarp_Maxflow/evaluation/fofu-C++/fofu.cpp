
#include "time.h"
#include <cstdio>
#include <queue>
#include <cstring>
#include <vector>
#include <iostream>
#include <fstream>

#define G_SIZE 10000

using namespace std;

vector<int> graph[G_SIZE];
int capacities[G_SIZE][G_SIZE];
int flowPassed[G_SIZE][G_SIZE];
int parentsList[G_SIZE];
int currentPathCapacity[G_SIZE];

//int** graph_init (int size) {
//	int** GRAPH = new int* [size];
//
//	int i;
//	for (i = 0; i < size; i++){
//		GRAPH[i] = new int [size];
//	}
//
//	return GRAPH;
//}
//
///* As our matrix is a int** we have to clean it up in a loop */
//void graph_free (int** GRAPH, int size) {
//	int i;
//	for (i = 0; i < size; i++) {
//		delete GRAPH[i];
//		for (int j = 0; j < size; j++)
//			GRAPH[i][j] = 0;
//	}
//
//	delete GRAPH;
//}

int stat_counter_ga = 0;
int stat_counter_mget = 0;

int bfs(int startNode, int endNode)
{
    memset(parentsList, -1, sizeof(parentsList));
    memset(currentPathCapacity, 0, sizeof(currentPathCapacity));

    queue<int> q;
    q.push(startNode);

    parentsList[startNode] = -2;
    currentPathCapacity[startNode] = 999;

    while(!q.empty())
    {
        int currentNode = q.front();
        q.pop();

        for(int i=0; i<graph[currentNode].size(); i++)
        {
            stat_counter_mget+=3;
            int to = graph[currentNode][i];
            if(capacities[currentNode][to] - flowPassed[currentNode][to] > 0)
            {
                stat_counter_ga++;
                if(parentsList[to] == -1)
                {
                    parentsList[to] = currentNode;
                    currentPathCapacity[to] = min(currentPathCapacity[currentNode],
                    capacities[currentNode][to] - flowPassed[currentNode][to]);
                    if(to == endNode)
                    {
                        return currentPathCapacity[endNode];
                    }
                    q.push(to);
                }
            }
        }
    }
    return 0;
}

int stat_outer_c = 0;

int edmondsKarp(int startNode, int endNode)
{
    int maxFlow = 0;
      while(true)
    {
        stat_outer_c++;
        int flow = bfs(startNode, endNode);
        if (flow == 0)
        {
            break;
        }
        maxFlow += flow;
        int currentNode = endNode;
        while(currentNode != startNode)
        {
            int previousNode = parentsList[currentNode];
            stat_counter_mget+=2;            
            flowPassed[previousNode][currentNode] += flow;
            flowPassed[currentNode][previousNode] -= flow;
            currentNode = previousNode;
        }
    }
    return maxFlow;
}

int main(int argc, char** argv) {
	if (argc < 2) {
		cout << "Usage: <GRAPH-PATH>\n";
	}
	else {
		ifstream fi(argv[1]);
		int V_size, E_size;
		fi >> V_size >> E_size;

		if (V_size > 0 && V_size <= G_SIZE) {
			//capacities = graph_init(V_size);
			//flowPassed = graph_init(V_size);
			//parentsList = new int [V_size];
			//currentPathCapacity = new int [V_size];

			for (int i = 0; i < E_size; i++) {
				int from, to, capacity;
				fi >> from >> to >>capacity;

				capacities[from][to] = capacity;
				graph[from].push_back(to);

				graph[to].push_back(from);
			}

			clock_t tStart = clock();
			int maxFlow = edmondsKarp(0, V_size -1);

			printf("@@@time: %.0f ms\n", ((double)(clock() - tStart)/CLOCKS_PER_SEC) * 1000);
			printf("[Input (V E): %d %d]\n", V_size, E_size);
			printf("@@@max-flow: %d\n", maxFlow);
      printf("stat_outer_c: %d\n", stat_outer_c);
      printf("stat_counter_ga: %d\n", stat_counter_ga);
      printf("stat_counter_mget: %d\n", stat_counter_mget);


			//delete currentPathCapacity;
			//delete parentsList;
			//graph_free(flowPassed, V_size);
			//graph_free(capacities, V_size);

		}
		else {
			cout << "Input graph is invalid\n";
		}
	}

	return 0;
}
