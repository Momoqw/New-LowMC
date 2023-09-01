#include "LowMC.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <cstring>

#include <random>
#include <ctime>
using namespace std;

double C(int n, int m)
{
	if (m < n - m) m = n - m;
	double ans = 1;
	for (int i = m + 1; i <= n; i++) ans *= i;
	for (int i = 1; i <= n - m; i++) ans /= i;
	return ans;
}
LowMC::LowMC() {
	L = new M[R];
	IL = new M[R];
	KF = new M[R+1];
	CONS.resize(R);
	for (int i = 0; i < R; i++) {
		CONS[i].resize(N);
	}
	//load round constantC:\Users\anny\Desktop\lowMC_algebraicMITM-main1\lowMC_algebraicMITM-main\constant.txt
	ifstream con("constant.txt");
	for (int i = 0; i < R; i++) {
		bool a = 0;
		for (int j = 0; j < N; j++) {
			con >> a;
			CONS[i][j] = a;
		}
	}
	con.close();
	//load linear layers
	initializePars("newLinear.txt", 0, L);
	//load the inverse of the linear layers
	initializePars("invLinear.txt", 0, IL);
	//load the key schedule function
	initializePars("key.txt", 1, KF);

	bool checknon[N] = {
		0,1,1,1,1,0,0,1,1,1,1,0,1,1,1,0,1,1,0,1,0,1,0,0,1,1,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,0,1,1,1,1,0,1,1,1,0,1,1,1,1,1,0,0,1,1,1,1,1,1,1,0,0,1,0,1,0,0,0,1,0,1,1,1,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,0,0,1,0,0,0,1,0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,0,1,1,0,1,0,0,
	};

	/*M id;
	id.r = N;
	id.c = N;
	clearMatrix(id);
	matrixMul(L[102], IL[102], id);
	outputM(id);*/

	bool out[N];
	matrixMul(IL[102], checknon, out);
	bool gamma[N] = {
		0,1,0,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,1,0,0,1,1,1,0,0,1,1,0,0,0,1,0,1,0,0,0,1,1,0,0,1,1,0,1,0,1,1,0,0,1,0,0,1,1,1,1,1,1,1,0,1,1,0,1,0,0,1,1,0,0,1,0,1,0,0,1,1,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,0,0,0,0,1,0,0,1,1,1,0,0,1,0,0,1,1,0,1,0,1,1,0,
	};
	for (int i = 0; i < N; i++) {
		if (gamma[i] != out[i]) {
			cout << "wrong1" << endl;
		}
	}
}

LowMC::~LowMC() {
	delete[]L;
	delete[]IL;
	delete[]KF;
}

void LowMC::initializePars(string filename,bool isKey,M* mat) {
	ifstream in(filename);
	int length = R;
	if (isKey)
		length++;
	for (int i = 0; i < length; i++) {
		for (int j = 0; j < N; j++) {
			for (int k = 0; k < N; k++) {
				in >> mat[i].ma[j][k];
			}
		}
	}
	in.close();
}

/*****************************
*the encryption function
******************************/
void LowMC::encryptionDetails(bool p0[], bool k[], bool c[], int rounds, vector<vector<bool> > &LOut, vector<vector<bool> >& SOut){
	M rk;
	rk.r = R + 1;
	rk.c = N;

	bool* p1;
	p1 = new bool[N];
	for (int i = 0; i < N; i++) {
		p1[i] = p0[i];
	}

	for (int i = 0; i < R + 1; i++) {
		matrixMul(KF[i], k, rk.ma[i]);
	}
	//whitening key
	for (int i = 0; i < N; i++) {
		p1[i] = p1[i] ^ rk.ma[0][i];
	}

	int t[3];
	bool* pt = new bool[N];
	for (int i = 0; i < rounds; i++) {
		//s-box (only works for the first 3m bits)
		for (int j = 0; j < 1; j++) {
			t[0] = p1[3 * j] ^ (p1[1 + 3 * j] & p1[2 + 3 * j]);
			t[1] = p1[3 * j] ^ p1[1 + 3 * j] ^ (p1[3 * j] & p1[2 + 3 * j]);
			t[2] = p1[3 * j] ^ p1[1 + 3 * j] ^ p1[2 + 3 * j] ^ (p1[3 * j] & p1[1 + 3 * j]);
			p1[3 * j] = t[0];
			p1[3 * j + 1] = t[1];
			p1[3 * j + 2] = t[2];
		}
		//the value after SBox
		for (int j = 0; j < N; j++) {
			SOut[i][j] = p1[j];
		}

		//linear matrix
		matrixMul(L[i], p1, pt);

		//constant addition
		for (int j = 0; j < N; j++) {
			p1[j] = pt[j] ^ CONS[i][j];
		}

		//key addition
		for (int j = 0; j < N; j++) {
			p1[j] = p1[j] ^ rk.ma[i + 1][j];
		}

		for (int j = 0; j < N; j++) {
			LOut[i][j] = p1[j];
		}
	}
	for (int i = 0; i < N; i++) {
		c[i] = p1[i];
	}
	delete[]pt;
	delete[]p1;
}

/*****************************
*
*used for attacks
*
*****************************/

/****************************
*find the input difference such that the first r0 rounds contain no active S-boxes
*****************************/
void LowMC::findInputDifference(bool x[]) {
	int r0 = 42;
	
	M eq;
	eq.r = r0 * 3;
	eq.c = N + 1;
	clearMatrix(eq);
	int cnt = 0;

	M initState;
	initState.r = N;
	initState.c = N;
	clearMatrix(initState);
	for (int i = 0; i < N; i++) {
		initState.ma[i][i] = 1;
	}

	for (int i = 0; i < r0; i++) {
		//derive equations
		for (int j = 0; j < 3; j++) {
			for (int k = 0; k < initState.c; k++) {
				eq.ma[cnt][k] = initState.ma[j][k];
			}
			eq.ma[cnt][N] = 0;
			cnt++;
		}

		for (int j = 0; j < 3; j++) {
			for (int k = 0; k < initState.c; k++) {
				initState.ma[j][k] = 0;
			}
		}

		matrixMul(L[i], initState);
	}
	//gauss elimination
	gauss(eq, eq.c - 1);

	vector<vector<bool> > sol;
	sol.clear();
	int solNum = 0;
	storeSolutions(sol, eq, solNum);
	cout << "solutions of the input difference:" << endl;
	for (int i = 0; i < solNum; i++) {
		for (int j = 0; j < eq.c - 1; j++) {
			cout << sol[i][j] << ",";
		}
		cout << endl;
	}
}

/***********************************
*enumerate the difference forwards
************************************/
void LowMC::enumerateDiffForwards(bool x[]) {
	vector<vector<bool> > nonlin, lin;
	int total = 13;
	nonlin.resize(total + 1);
	lin.resize(total + 1);
	for (int i = 0; i < total+1; i++) {
		nonlin[i].resize(N);
		lin[i].resize(N);
	}
	int current = 0;
	for (int i = 0; i < N; i++) {
		lin[0][i] = x[i];
	}
	vector<bool> u;
	u.resize(3 * total);
	vector<vector<bool> > Dh;
	Dh.clear();forwards(current, total, Dh, u, nonlin, lin);
	cout << "total size: "<<dec << Dh.size() << endl;

	cout << "writing to files..." << endl;
	ofstream uValue("uvalue.txt");
	for (int i = 0; i < Dh.size(); i++) {
		for (int j = 0; j < u.size(); j++) {
			uValue << Dh[i][j] << " ";
			//cout << Dh[i][j] << " ";
		}
		//cout << endl;
		uValue << endl;
	}
	uValue.close();
	cout << "writing to files ends" << endl;

	/*int DhSize = Dh.size();
	for (int i = 0; i < DhSize; i++) {
		Dh[i].clear();
	}
	Dh.clear();*/
}

void LowMC::forwards(int current, int total, vector<vector<bool>>& Dh, vector<bool>& u, vector<vector<bool> >& nonlin, vector<vector<bool> >& lin) {
	if (current == total) {
		//record the output differences of the S-box
		Dh.push_back(u);
		if (Dh.size() % 0x10000 == 0) {
			cout << hex << Dh.size() << endl;
		}
		return;
	}

	int r0 = 42;
	int input = lin[current][0] + 2 * lin[current][1] + 4 * lin[current][2];
	int size = 4, output = 0;
	if (input == 0)
		size = 1;

	for (int i = 3; i < N; i++) {//difference through the identity mapping
		nonlin[current + 1][i] = lin[current][i];
	}
	for (int i = 0; i < size; i++) {//difference through the nonlinear part
		output = ddt[input][i];
		nonlin[current + 1][0] = output & 0x1;
		nonlin[current + 1][1] = (output>>1) & 0x1;
		nonlin[current + 1][2] = (output >> 2) & 0x1;
		u[3 * current] = nonlin[current + 1][0];
		u[3 * current + 1] = nonlin[current + 1][1];
		u[3 * current + 2] = nonlin[current + 1][2];
		matrixMul(L[current + r0], nonlin[current + 1], lin[current + 1]);
		forwards(current + 1, total, Dh, u, nonlin, lin);
	}
}
void LowMC::forwards1( int total,  vector<vector<bool> >& nonlin, bool u[], vector<vector<bool> >& lin) {
	int m = 1;
	int cnt = 0;
	int r0 = 42;
	for (int i = 0; i < 13; i++) {
		//replace equations with new variables
		
			nonlin[i + 1][0] = u[3 * i ];
			nonlin[i + 1][1] = u[3 * i+1];
			nonlin[i + 1][2] = u[3 * i+2];
			for (int j = 0; j < 125; j++)
			{
				nonlin[i + 1][j + 3] = lin[i ][j + 3];
		}
		//linear transform
		matrixMul(L[i + r0], nonlin[i + 1], lin[i + 1]);
	}
}
/*************************************
*enumerate the difference backwards
**************************************/
void LowMC::enumerateDiffBackwards(bool x[]) {
	vector<vector<bool> > nonlin, lin;
	int total = 13;
	nonlin.resize(total + 1);
	lin.resize(total + 1);
	for (int i = 0; i < total + 1; i++) {
		nonlin[i].resize(N);
		lin[i].resize(N);
	}
	int current = 0;
	for (int i = 0; i < N; i++) {
		lin[0][i] = x[i];
	}

	unsigned int cnt[2] = { 0,0 };
	backwards(cnt,current, total, nonlin, lin);
	cout << hex << "time complexity: 0x" << cnt[1] << endl;

	for (int i = 0; i < 0x800000; i++) {
		DH[i].clear();
	}
	DH.clear();
}

void LowMC::backwards(unsigned int cnt[], int current, int total, vector<vector<bool> >& nonlin, vector<vector<bool> >& lin) {
	int r = 102;//103 rounds
	if (current == total) {
		cnt[0]++;
		//record the output differences of the S-box (gamma): gamma=lin[current]
		vector<bool> gamma(N);
		matrixMul(IL[r - current], lin[current], gamma);
		cnt[1] += onlineCheck(DH,QQ1,PP0,gamma);
		if (cnt[0] % 0x10000==0) {
			cout << hex << cnt[0] << endl;
		}
		return;
	}

	
	matrixMul(IL[r - current], lin[current], nonlin[current + 1]);

	int input = nonlin[current+1][0] + 2 * nonlin[current+1][1] + 4 * nonlin[current+1][2];
	int size = 4, output = 0;
	if (input == 0)
		size = 1;

	for (int i = 3; i < N; i++) {//difference through the identity mapping
		lin[current + 1][i] = nonlin[current+1][i];
	}

	for (int i = 0; i < size; i++) {//difference through the nonlinear part
		output = ddt[input][i];
		lin[current + 1][0] = output & 0x1;
		lin[current + 1][1] = (output >> 1) & 0x1;
		lin[current + 1][2] = (output >> 2) & 0x1;
		backwards(cnt,current + 1, total, nonlin, lin);
	}
}

/*
x[] is the state difference \Delta_{r0}
*/

void LowMC::constructPQ(bool x[]) {
	int r0 = 42;
	int r1 = 48;
	int r2 = 13;
	int l = 47;//r1=48, l=r1-1=47
	int t = 13;
	int q = 3 * t;
	int M1Cols = 3 * P * l - q;
	int M1Rows = N - 3 * P;
	//construct a coefficient matrix of size, whose #row is D
	M m;
	m.r = N, m.c = 3 * l + 1;//m.c=142
	clearMatrix(m);

	//initialize the last column of m
	for (int i = 0; i < N; i++) {
		m.ma[i][m.c - 1] = x[i];
	}

	int cnt = 0;//counter for the variables
	for (int i = 0; i < l; i++) {
		//replace equations with new variables
		for (int j = 0; j < 3 * P; j++) {
			for (int k = 0; k < cnt; k++) {//first clear
				m.ma[j][k] = 0;
			}
			m.ma[j][cnt] = 1;//replace with a new variable v[cnt];
			m.ma[j][m.c - 1] = 0;
			cnt++;
		}
		matrixMul(L[i + r0], m);//linear transform
	}
	outputM(m);
	M MM, M1, Q0, Q1;
	MM.r = D;
	MM.c = m.c;
	clearMatrix(MM);
	for (int i = 0; i < MM.r; i++)
		for (int j = 0; j < MM.c; j++)
			MM.ma[i][j] = m.ma[i + 3 * P][j];

	M1.r = MM.r;
	M1.c = M1Cols + MM.r;
	clearMatrix(M1);
	for (int i = 0; i < MM.r; i++) {
		for (int j = 0; j < M1Cols; j++) {
			M1.ma[i][j] = MM.ma[i][j + q];
		}
		M1.ma[i][M1Cols + i] = 1;
	}
	//outputM(M1);
	//cout << "after gauss:" << endl;
	gauss(M1, M1.c);
	simplify(M1, M1.c);
	gauss(MM, MM.c);
	simplify(MM, MM.c);
	outputM(MM);
	outputM(M1);
	//M1.c = M1Cols;
	//outputM(M1);

	Q1.r = M1.r, Q0.r = M1.r;
	Q1.c = M1.r, Q0.c = M1Cols;
	clearMatrix(Q0), clearMatrix(Q1);
	for (int i = 0; i < M1.r; i++) {
		for (int j = 0; j < M1Cols; j++) {
			Q0.ma[i][j] = M1.ma[i][j];
		}
		for (int j = 0; j < M1.r; j++) {
			Q1.ma[i][j] = M1.ma[i][j + M1Cols];
		}
	}

	//output the transform matrix Q1
	M p;
	p.r = MM.r, p.c = MM.c;
	matrixMul(Q1, MM, p);
	cout << "P:" << endl;
	outputM(p);

	M P0;
	P0.r = p.r, P0.c = q;
	for (int i = 0; i < p.r; i++) {
		for (int j = 0; j < q; j++) {
			P0.ma[i][j] = p.ma[i][j];
		}
	}
	cout << "P0:" << endl;
	outputM(P0);

	M P0P;
	P0P.r = 23;
	P0P.c = P0.c;
	clearMatrix(P0P);
	for (int i = 0; i < 23; i++) {
		for (int j = 0; j < P0.c; j++) {
			P0P.ma[i][j] = P0.ma[i + P0.r - 23][j];
		}
	}

	vector<bool> cbit(P0P.r);
	for (int i = 0; i < P0P.r; i++) {
		cbit[i] = p.ma[i + P0.r - 23][p.c - 1];
	}

	/*
	bool uv[141] = {
		1,1,0,0,1,1,0,1,0,1,1,0,0,0,0,1,0,1,0,0,1,0,0,0,1,1,1,0,0,0,0,0,0,1,0,1,1,0,1,1,0,1,0,0,1,1,1,1,1,0,1,1,0,1,1,0,0,1,0,0,1,1,0,0,1,1,1,0,0,0,0,0,0,0,1,0,0,1,1,0,1,0,1,0,0,1,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,1,1,0,1,0,1,1,0,1,0,0,0,1,1,0,0,1,0,
	};
	bool gamma[125] = {
		1,0,0,0,1,1,0,1,1,1,1,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,1,1,1,1,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,1,0,
	};

	bool uvRes[125];
	p.c = p.c - 1;//remove the constart part
	matrixMul(p, uv, uvRes);
	p.c = p.c + 1;
	bool gRes[125];
	matrixMul(Q1, gamma, gRes);

	for (int i = 0; i < 125; i++) {
		uvRes[i] = uvRes[i]^p.ma[i][p.c-1];
	}
	for (int i = 125-23; i < 125; i++) {
		//cout << (uvRes[i] ^ gRes[i]);
		cout << uvRes[i];
	}
	cout << endl;
	*/
	//the above test is passed

	PP0.r = P0.r, PP0.c = P0.c + 1;
	QQ1.r = Q1.r, QQ1.c = Q1.c;
	matrixEq(Q1, QQ1);
	PP0.c = P0.c;
	matrixEq(P0, PP0);
	PP0.c = P0.c + 1;//store the constant bit, epsilon
	for (int i = 0; i < PP0.r; i++)
		PP0.ma[i][PP0.c - 1] = p.ma[i][p.c - 1];
	//system("pause");

	vector<vector<unsigned long long> > Dh;
	Dh.resize(0x800000);
	storeSolutions(Dh, P0P, cbit);

	//store Dh
	DH.resize(0x800000);
	for (int i = 0; i < DH.size(); i++) {
		DH[i].clear();
		for (int j = 0; j < Dh[i].size(); j++) {
			DH[i].push_back(Dh[i][j]);
		}
	}

	cbit.clear();
	for (int i = 0; i < 0x800000; i++) {
		Dh[i].clear();
	}
	Dh.clear();
}

void LowMC::storeSolutions(vector<vector<unsigned long long>>& Dh, M& P0P, vector <bool>& cbit) {
	//need a full re-write
	const int size = 23;
	const int q = 3 * 13;
	bool u[q];
	for (int i = 0; i < q; i++)
		u[i] = 0;
	//use P0P and cbit to precompute the right-hand of equations
	bool beta[size];

	ifstream uvalue("uvalue.txt");
	const int DhSize = 17134432;
	bool checkU[39] = {
		1,1,0,0,1,1,0,1,0,1,1,0,0,0,0,1,0,1,0,0,1,0,0,0,1,1,1,0,0,0,0,0,0,1,0,1,1,0,1,
	};
	for (int i = 0; i < DhSize; i++) {
		for (int j = 0; j < q; j++) {
			uvalue >> u[j];
		}
		matrixMul(P0P, u, beta);
		for (int j = 0; j < size; j++) {
			beta[j] = beta[j] ^ cbit[j];
		}
		//store uRes[0,1,...,17] according to uRes[18,19,...,40]
		unsigned long long in = 0, res = 0,one=1;
		for (int j = 0; j < size; j++) {
			in = in | (beta[j] << j);
		}
		for (int j = 0; j < q; j++) {
			if (u[j] == 1) {
				res = res | (one << j);
			}
		}
		Dh[in].push_back(res);

		/*bool check = true;
		for (int j = 0; j < q; j++) {
			if (u[j] != checkU[j]) {
				check = false;
				break;
			}
		}

		if (check) {
			for (int j = 0; j < size; j++) {
				cout << beta[j];
			}
			cout << endl;
			//indexBeta = in;
			//cout << "correctIndex:" << in << endl;
			//cout << "correctVal:" << hex << res << endl;
		}*/
	}
	uvalue.close();
	cout << "contructing Dh (the table D_u in the paper) is over" << endl;

	//online phase
	
}
/********************************
*the online phase
*********************************/
void LowMC::constructdinur( bool ga[],bool x[])
{
	
	int r0 = 42;
	int r1 = 48;
	int r2 = 13;
	int l = 47;//r1=48, l=r1-1=47
	int t = 13;
	const int q = 3 * 13;
	int M1Cols = 3 * P * l - q;
	int M1Rows = N - 3 * P;
	//construct a coefficient matrix of size, whose #row is D
	M m;
	m.r = N, m.c = 3 * l + 1;//m.c=142
	clearMatrix(m);

	//initialize the last column of m
	for (int i = 0; i < N; i++) {
		m.ma[i][m.c - 1] = x[i];
	}

	int cnt = 0;//counter for the variables
	for (int i = 0; i < l; i++) {
		//replace equations with new variables
		for (int j = 0; j < 3 * P; j++) {
			for (int k = 0; k < cnt; k++) {//first clear
				m.ma[j][k] = 0;
			}
			m.ma[j][cnt] = 1;//replace with a new variable v[cnt];
			m.ma[j][m.c - 1] = 0;
			cnt++;
		}
		matrixMul(L[i + r0], m);//linear transform
	}
	/*cout << "m:" << endl;
	outputM(m);*/
	M MM, M1, Q0, Q1;
	MM.r = D;
	MM.c = m.c;
	clearMatrix(MM);
	for (int i = 0; i < MM.r; i++)
		for (int j = 0; j < MM.c; j++)
			MM.ma[i][j] = m.ma[i + 3 * P][j];
	/*cout << "MM:" << endl;
	outputM(MM);*/
	M1.r = MM.r;
	M1.c = M1Cols + MM.r;
	clearMatrix(M1);
	for (int i = 0; i < MM.r; i++) {
		for (int j = 0; j < M1Cols; j++) {
			M1.ma[i][j] = MM.ma[i][j + q];
		}
		M1.ma[i][M1Cols + i] = 1;
	}
	/*cout << "M1:" << endl;
	outputM(M1);
	cout << "after gauss:" << endl;*/
	gauss(M1, M1.c);
	simplify(M1, M1.c);
	gauss(MM, MM.c);
	simplify(MM, MM.c);
	//M1.c = M1Cols;
	//outputM(M1);

	Q1.r = M1.r, Q0.r = M1.r;
	Q1.c = M1.r, Q0.c = M1Cols;
	clearMatrix(Q0), clearMatrix(Q1);
	for (int i = 0; i < M1.r; i++) {
		for (int j = 0; j < M1Cols; j++) {
			Q0.ma[i][j] = M1.ma[i][j];
		}
		for (int j = 0; j < M1.r; j++) {
			Q1.ma[i][j] = M1.ma[i][j + M1Cols];
		}
	}

	//output the transform matrix Q1
	M p;
	p.r = MM.r, p.c = MM.c;
	matrixMul(Q1, MM, p);
	/*cout << "P:" << endl;
	outputM(p);*/

	M P0;
	P0.r = p.r, P0.c = q;
	for (int i = 0; i < p.r; i++) {
		for (int j = 0; j < q; j++) {
			P0.ma[i][j] = p.ma[i][j];
		}
	}
	/*cout << "P0:" << endl;
	outputM(P0);*/

	M P0P;
	P0P.r = 23;
	P0P.c = P0.c;
	clearMatrix(P0P);
	for (int i = 0; i < 23; i++) {
		for (int j = 0; j < P0.c; j++) {
			P0P.ma[i][j] = P0.ma[i + P0.r - 23][j];
		}
	}

	vector<bool> cbit(P0P.r);
	for (int i = 0; i < P0P.r; i++) {
		cbit[i] = p.ma[i + P0.r - 23][p.c - 1];
	}
	/*
	bool uv[141] = {
		1,1,0,0,1,1,0,1,0,1,1,0,0,0,0,1,0,1,0,0,1,0,0,0,1,1,1,0,0,0,0,0,0,1,0,1,1,0,1,1,0,1,0,0,1,1,1,1,1,0,1,1,0,1,1,0,0,1,0,0,1,1,0,0,1,1,1,0,0,0,0,0,0,0,1,0,0,1,1,0,1,0,1,0,0,1,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,1,1,0,1,0,1,1,0,1,0,0,0,1,1,0,0,1,0,
	};
	bool gamma[125] = {
		1,0,0,0,1,1,0,1,1,1,1,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,1,1,1,1,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,1,0,
	};

	bool uvRes[125];
	p.c = p.c - 1;//remove the constart part
	matrixMul(p, uv, uvRes);
	p.c = p.c + 1;
	bool gRes[125];
	matrixMul(Q1, gamma, gRes);

	for (int i = 0; i < 125; i++) {
		uvRes[i] = uvRes[i]^p.ma[i][p.c-1];
	}
	for (int i = 125-23; i < 125; i++) {
		//cout << (uvRes[i] ^ gRes[i]);
		cout << uvRes[i];
	}
	cout << endl;
	*/
	//the above test is passed
	const int size = 23;
	
	bool u[q];
	for (int i = 0; i < q; i++)
		u[i] = 0;
	//use P0P and cbit to precompute the right-hand of equations
	bool beta[size];

	ifstream uvalue("uvalue.txt");
	ofstream uValue1("uvalue1.txt");
	const int DhSize = 17134432;
	int g = 0;
	for (int i = 0; i < DhSize; i++) {
		for (int j = 0; j < q; j++) {
			uvalue >> u[j];
		}
		matrixMul(P0P, u, beta);
		for (int j = 0; j < size; j++) {
			beta[j] = beta[j] ^ cbit[j];
		}
		
		bool arraysEqual = true; // 标志变量
		int count = 0; //循环控制变量
		//确定元素是否包含相同的数据
		while (arraysEqual && count < 23)
		{
			if (beta[count] != ga[count+102])
				arraysEqual = false;
			count++;
		}
		//显示合适的消息
		bool u1[N];
		if (arraysEqual)
		{
			g++;
			vector<vector<bool> > nonlin, lin;
			int total = 13;
			nonlin.resize(total + 1);
			lin.resize(total + 1);
			for (int i = 0; i < total + 1; i++) {
				nonlin[i].resize(N);
				lin[i].resize(N);
			}
			int current = 0;
			for (int i = 0; i < N; i++) {
				lin[0][i] = x[i];
			}
			forwards1(  total, nonlin, u, lin);
			
			for (int i = 3; i < N; i++)
			{
				u1[i] = nonlin[13][i];
			}
			for (int i = 0; i < 3; i++)
			{
				u1[i] = u[i + q-3];
			}
			
		
				for (int j = 0; j < N; j++) {
					uValue1 << u1[j] << " ";				
				}			
				uValue1 << endl;	
		
		}

	}
	uValue1.close();
	uvalue.close();
	cout << "the number of uvalue1=" << g << endl;
}
void LowMC::constructForwardDiffR1( bool ga[]) {
	//check the first 3m bits of inputDiff: inputDiff[0,1,...,3m-1]
	//introudce at most 2m variables in the first round
	//introduce 3*(r1-2)*m variables in the next r1-2 rounds
	//connect the output difference in the last round
	
	

	
	ifstream uvalue1("uvalue1.txt");
	
	bool u1[N] = {};
	
	
	
	for (int i = 0; i < N; i++)
	{
		u1[i] = 0;
	}
	//ccc represent the number of (u_1,u_2...,u_3t)
	for (int ccc = 0; ccc < 5; ccc++) {
		
		
		for (int j = 0; j < N; j++) {
			uvalue1 >> u1[j];
		}
		cout << "u1:" << endl;
		for (int k = 0; k < N; k++)
		{
			cout << u1[k];
		}
		cout << endl;
		int r0 = 42;
		int r1 = 48;
		int m = 1;
		int t = 13;
		int s = 102;
		M eq;
		eq.r = N;
		eq.c = 3 * m * (r1 - 1) - 3 * t + 1;//eq.c=2+15+1=18 for r1=7,m=1
		
		M zq;
		zq.r = N;
		zq.c = 3 * m * (r1 - 1) - 3 * t + 1;
		M zq1;
		zq1.r = N;
		zq1.c = 3 * m * (r1 - 1) - 3 * t + 1;
		
		
		
		
		for (int jjj = 25; jjj > 15; jjj--)
		{


			clearMatrix(eq);
			clearMatrix(zq);
			clearMatrix(zq1);
			
			
			//matrix start;

			//the first round
			//the variables are chosen accorinding to the input difference
			int cnt = 0;//the indices of variables

			for (int i = 0; i < N; i++) {
				eq.ma[i][eq.c - 1] = u1[i];
			}
			//apply the linear transform
			matrixMul(L[r0 + 12], eq);
			//output eq
			//cout << "eq:" << endl;
			//outputMatrix(eq);

			


			//the next 34 rounds



			for (int i = 0; i < r1 - jjj; i++) {
				//replace equations with new variables
				for (int j = 0; j < 3 * m; j++) {
					for (int k = 0; k < cnt; k++) {//first clear
						eq.ma[j][k] = 0;
					}
					eq.ma[j][cnt] = 1;//replace with a new variable v[cnt];
					eq.ma[j][eq.c - 1] = 0;
					cnt++;
				}
				//linear transform
				matrixMul(L[i + r0 + 13], eq);
			}



			for (int m = 0; m < N; m++)
			{
				for (int j = 0; j < eq.c; j++)
				{
					zq.ma[m][j] = eq.ma[m][j];
				}
			}


			for (int j = 0; j < 3 * m; j++) {
				for (int k = 0; k < cnt; k++) {//first clear
					eq.ma[j][k] = 0;
				}
				eq.ma[j][cnt] = 1;//replace with a new variable v[cnt];
				eq.ma[j][eq.c - 1] = 0;
				cnt++;
			}


			for (int m = 0; m < N; m++)
			{
				for (int j = 0; j < eq.c; j++)
				{
					zq1.ma[m][j] = eq.ma[m][j];
				}
			}


			//linear transform
			matrixMul(L[r1 - jjj + r0 + 13], eq);

			for (int i = jjj - 1; i >= 15; i--)
			{
				for (int j = 0; j < 3 * m; j++) {
					for (int k = 0; k < cnt; k++) {//first clear
						eq.ma[j][k] = 0;
					}
					eq.ma[j][cnt] = 1;//replace with a new variable v[cnt];
					eq.ma[j][eq.c - 1] = 0;
					cnt++;
				}
				//linear transform
				matrixMul(L[r1 - i + r0 + 13], eq);
			}
			
			cout << "eq:" << endl;
			outputM(eq);
			cout << endl;
			gauss(eq, eq.c - 1);
			cout << "after gauss:" << endl;
			cout << "eq:" << endl;
			outputM(eq);
			cout << endl;
			
			M connectPart;
			//matrix connectPart;
			connectPart.r = s;
			connectPart.c = eq.c;
			int varNum = eq.c - 1;
			clearMatrix(connectPart);
			for (int i = 0; i < s; i++) {
				for (int j = 0; j < eq.c; j++) {
					connectPart.ma[i][j] = eq.ma[i + 3 * m][j];
				}

			}
			for (int i = 0; i < s; i++)
			{
				connectPart.ma[i][eq.c - 1] ^= ga[i];
			}


			gauss(connectPart, varNum);
			/*
			cout << "connectPart:" << endl;
			outputM(connectPart);
			cout << endl;
			*/


			M mq;
			mq.r = s;
			mq.c = 3 * m * (r1 - 1) - 3 * t + 1;
			clearMatrix(mq);

			for (int i = 0; i < s; i++)

			{
				for (int j = 0; j < mq.c; j++)
				{
					mq.ma[i][j] = connectPart.ma[i][j];
				}

			}
			/*
			cout << "mq:" << endl;
			outputM(mq);
			cout << endl;
			*/
			gauss(mq, mq.c - 1);
			simplify(mq, mq.c - 1);
			/*
			cout << "mq:" << endl;
			outputM(mq);
			cout << endl;
			*/
			//mark the free variables
			
			int totalVars = 3 * m * (r1 - 1) - 3 * t;
			
			vector<bool> freeVar(totalVars);
			vector<int> index(totalVars);
			for (int j = 0; j < totalVars; j++)
			{
				index[j] = 0;
			}
			for (int i = 0; i < totalVars; i++)
				freeVar[i] = 1;
			for (int i = 0; i < mq.r; i++) {
				for (int j = i; j < mq.c - 1; j++) {
					if (mq.ma[i][j] == 1) {
						freeVar[j] = 0;
						index[j] = i;//record the expression for the variable u_j, i.e. the i-th row
						break;
					}
				}
			}
			int freeVarCnt = 0;
			for (int i = 0; i < freeVar.size(); i++) {
				if (freeVar[i])
					freeVarCnt++;
			}

			//cout << "the number of free variables:" << freeVarCnt << " \t #terms:" << freeVarCnt + (freeVarCnt * (freeVarCnt - 1) / 2) + (freeVarCnt * (freeVarCnt - 1) * (freeVarCnt - 2) / 6) << endl;
			
			//update eq
			/*
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < eq.c - 1; j++) {
					if (eq.ma[i][j] == 1 && freeVar[j] == 0) {
						eq.ma[i][j] = 0;//update it
						for (int k = j + 1; k < eq.c; k++) {
							eq.ma[i][k] = eq.ma[i][k] ^ mq.ma[index[j]][k];
						}
					}
				}
			}
			*/
			/*
			cout << "eq:" << endl;
			outputM(eq);
			cout << endl;
			*/
			//update zq
			/*
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < zq.c - 1; j++) {
					if (zq.ma[i][j] == 1 && freeVar[j] == 0) {
						zq.ma[i][j] = 0;//update it
						for (int k = j + 1; k < zq.c; k++) {
							zq.ma[i][k] = zq.ma[i][k] ^ mq.ma[index[j]][k];
						}
					}
				}
			}
			*/
			/*
			cout << "zq:" << endl;
			outputM(zq);
			cout << endl;
			*/
			//update zq1
			/*
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < zq1.c - 1; j++) {
					if (zq1.ma[i][j] == 1 && freeVar[j] == 0) {
						zq1.ma[i][j] = 0;//update it
						for (int k = j + 1; k < zq1.c; k++) {
							zq1.ma[i][k] = zq1.ma[i][k] ^ mq.ma[index[j]][k];
						}
					}
				}
			}
			*/
			/*
			cout << "zq1:" << endl;
			outputM(zq1);
			cout << endl;
			*/
			/*
			vector<int> mapIndex(totalVars), inverseMap(totalVars);
			int rvar = 0;
			for (int i = 0; i < totalVars; i++) {
				if (freeVar[i]) {
					mapIndex[i] = rvar;
					inverseMap[rvar] = i;
					rvar++;
				}
			}
			
			M1 right;
			right.r = 3 * m;
			right.c = totalVars + 1;
			clearMatrix(right);
			*/
			M left1;
			left1.r = 3 * m;
			left1.c = totalVars + 1;
			clearMatrix(left1);
			M right1;
			right1.r = 3 * m;
			right1.c = totalVars + 1;
			clearMatrix(right1);


			/*
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < eq.c - 1; j++) {
					
						right.ma[i][j] = eq.ma[i][j];
					
				}
				right.ma[i][right.c - 1] = eq.ma[i][eq.c - 1];
			}
			*/
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < zq.c - 1; j++) {
					
						left1.ma[i][j] = zq.ma[i][j];
					
				}
				left1.ma[i][left1.c - 1] = zq.ma[i][zq.c - 1];
			}
			for (int i = 0; i < 3 * m; i++) {
				for (int j = 0; j < zq1.c - 1; j++) {
					
						right1.ma[i][j] = zq1.ma[i][j];
					
				}
				right1.ma[i][right1.c - 1] = zq1.ma[i][zq1.c - 1];
			}




			/*
			cout << "right:" << endl;
			outputM(right1);
			cout << endl;
			cout << "left:" << endl;
			outputM(right1);
			cout << endl;
			*/
			



			int quTerms = totalVars + (totalVars * (totalVars - 1) / 2) + (totalVars * (totalVars - 1) * (totalVars - 2) / 6);
			cout << "quTerms=" << quTerms << endl;
			//construct quadratic equations
			bool cubic[2][176954];
			bool Cubic[2][176954];
			for (int i = 0; i < 2; i++) {
				for (int j = 0; j < 176954; j++) {
					cubic[i][j] = 0;
				}
			}
			for (int i = 0; i < 2; i++) {
				for (int j = 0; j < 176954; j++) {
					Cubic[i][j] = 0;
				}
			}
			cout << "jjj=" << jjj << endl;
			cout << 123 << endl;
			for (int i = 0; i < 1; i++)
			{
				int j = 0;
				int k = 0;

				addLinear1(cubic, k, left1, j);
				

				addLinear1(cubic, k, left1, j + 1);
				

				addLinear1(cubic, k, left1, j + 2);
				

				addQuadratic1(cubic, k, left1, j, left1, j + 1, totalVars);
				

				addQuadratic1(cubic, k, left1, j, left1, j + 2, totalVars);
				

				addQuadratic1(cubic, k, left1, j + 1, left1, j + 2, totalVars);
				

				addCubic(cubic, k, left1, j, left1, j + 1, left1, j + 2, totalVars);
				
				k++;
				
				addLinear1(cubic, k, left1, j);
				
				addLinear1(cubic, k, left1, j + 1);
				
				addLinear1(cubic, k, left1, j + 2);
				
				addQuadratic1(cubic, k, left1, j, left1, j + 1, totalVars);
				
				addQuadratic1(cubic, k, left1, j, left1, j + 2, totalVars);
				
				addQuadratic1(cubic, k, left1, j + 1, left1, j + 2, totalVars);
				
				addCubic(cubic, k, left1, j, left1, j + 1, left1, j + 2, totalVars);
				
				for (int i = 0; i < 2; i++) {
					for (int j = 0; j < 176954; j++) {
						cout<<cubic[i][j] ;
					}
					cout << endl;
				}
				cout << endl;

			}
			
			
			cout << 123 << endl;
			for (int i = 0; i < 1; i++)
			{
				int j = 0;
				int k = 0;
				
				addLinear1(Cubic, k, right1, j);
				addLinear1(Cubic, k, right1, j + 1);
				addLinear1(Cubic, k, right1, j + 2);
				addQuadratic1(Cubic, k, right1, j, right1, j + 1, totalVars);
				addQuadratic1(Cubic, k, right1, j, right1, j + 2, totalVars);
				addQuadratic1(Cubic, k, right1, j + 1, right1, j + 2, totalVars);
				addCubic(Cubic, k, right1, j, right1, j + 1, right1, j + 2, totalVars);
				k++;


				
				addQuadratic1(Cubic, k, right1, j, right1, j, totalVars);
				addQuadratic1(Cubic, k, right1, j + 1, right1, j + 1, totalVars);
				addQuadratic1(Cubic, k, right1, j + 2, right1, j + 2, totalVars);
				cout << "Cubic=" << endl;
				for (int i = 0; i < 2; i++) {
					for (int j = 0; j < 176954; j++) {
						cout << Cubic[i][j];
					}
					cout << endl;
				}
				cout << endl;


			}
			
		}

		






	}
	uvalue1.close();
}
void LowMC::addLinear1(bool qeq[][176954], int row, M& lin, int index) {
	for (int i = 0; i < lin.c - 1; i++) {//variable part
		qeq[row][i] ^= lin.ma[index][i];
	}
	qeq[row][176954 - 1] ^= lin.ma[index][lin.c - 1];//constant part
}

void LowMC::addQuadratic1(bool qeq[][176954], int row, M& fac0, int in0, M& fac1, int in1, int total) {
	//(f0+a) & (f1+b) = f0f1 + b*f0 + a*f1 + ab
	if (fac0.ma[in0][fac0.c - 1]) {//a=1, add f1
		for (int i = 0; i < fac1.c - 1; i++) {//variable part
			qeq[row][i] ^= fac1.ma[in1][i];
		}
	}

	if (fac1.ma[in1][fac1.c - 1]) {
		for (int i = 0; i < fac0.c - 1; i++) {//variable part
			qeq[row][i] ^= fac0.ma[in0][i];
		}
	}

	qeq[row][176954 - 1] = qeq[row][176954 - 1] ^ (fac0.ma[in0][fac0.c - 1] & fac1.ma[in1][fac1.c - 1]);

	//add f0*f1
	for (int i = 0; i < fac0.c - 1; i++) {
		for (int j = 0; j < fac1.c - 1; j++) {
			if (fac0.ma[in0][i] == 1 && fac1.ma[in1][j] == 1) {
				//the term x_i*x_j
				int i0 = i, j0 = j;//(j0>=i0 is necessary)
				if (i0 > j0) {
					int t = i0;
					i0 = j0;
					j0 = t;
				}
				int index = (total + (total - (j0 - i0) + 1)) * (j0 - i0) / 2 + i0;
				if (index >= 176954) {
					cout << "i,j:" << i << " , " << j << endl;
					cout << "wrong8" << endl;
				}
				if (index < 0) {
					cout << "minus" << endl;
				}
				qeq[row][index] ^= 1;
			}
		}
	}
}
void LowMC::addCubic(bool qeq[][176954], int row, M& fac0, int in0, M& fac1, int in1, M& fac2, int in2, int total)
{//(f0+a)&(f1+b)&(f2+c)=f0f1f2+c*f0f1+b*f0f2+a*f1f2+ab*f2+ac*f1+bc*f0+abc
	if (fac0.ma[in0][fac0.c - 1])
	{//a=1,add f1f2
		for (int i = 0; i < fac1.c - 1; i++) {
			for (int j = 0; j < fac2.c - 1; j++) {
				if (fac1.ma[in1][i] == 1 && fac2.ma[in2][j] == 1) {
					//the term x_i*x_j
					int i0 = i, j0 = j;//(j0>=i0 is necessary)
					if (i0 > j0) {
						swap(i0, j0);
					}
					int index = (total + (total - (j0 - i0) + 1)) * (j0 - i0) / 2 + i0;
					if (index >= 176954) {
						cout << "i,j:" << i << " , " << j << endl;
						cout << "wrong1" << endl;
					}
					if (index < 0) {
						cout << "minus" << endl;
					}
					qeq[row][index] ^= 1;
				}
			}
		}

	}

	if (fac1.ma[in1][fac1.c - 1]) {//b=1,add f0f2,f2
		for (int i = 0; i < fac0.c - 1; i++) {
			for (int j = 0; j < fac2.c - 1; j++) {
				if (fac0.ma[in0][i] == 1 && fac2.ma[in2][j] == 1) {
					//the term x_i*x_j
					int i0 = i, j0 = j;//(j0>=i0 is necessary)
					if (i0 > j0) {
						swap(i0, j0);
					}
					int index = (total + (total - (j0 - i0) + 1)) * (j0 - i0) / 2 + i0;

					if (index >= 176954) {
						cout << "i,j:" << i << " , " << j << endl;
						cout << "wrong2" << endl;
					}
					if (index < 0) {
						cout << "minus" << endl;
					}
					qeq[row][index] ^= 1;
				}
			}
		}
		for (int i = 0; i < fac2.c - 1; i++) {//variable part
			qeq[row][i] ^= fac2.ma[in2][i];
		}
	}

	if (fac2.ma[in2][fac1.c - 1])
	{//c=1,add f0f1,f1,f0
		for (int i = 0; i < fac0.c - 1; i++) {
			for (int j = 0; j < fac1.c - 1; j++) {
				if (fac0.ma[in0][i] == 1 && fac1.ma[in1][j] == 1) {
					//the term x_i*x_j
					int i0 = i, j0 = j;//(j0>=i0 is necessary)
					if (i0 > j0) {
						swap(i0, j0);
					}
					int index = (total + (total - (j0 - i0) + 1)) * (j0 - i0) / 2 + i0;

					if (index >= 176954) {
						cout << "i,j:" << i << " , " << j << endl;
						cout << "wrong3" << endl;
					}
					if (index < 0) {
						cout << "minus" << endl;
					}
					qeq[row][index] ^= 1;
				}
			}
		}


		for (int i = 0; i < fac1.c - 1; i++) {//variable part
			qeq[row][i] ^= fac1.ma[in1][i];
		}

		for (int i = 0; i < fac0.c - 1; i++) {//variable part
			qeq[row][i] ^= fac0.ma[in0][i];
		}

	}

	qeq[row][176954 - 1] = qeq[row][176954 - 1] ^ (fac0.ma[in0][fac0.c - 1] & fac1.ma[in1][fac1.c - 1] & fac2.ma[in2][fac2.c - 1]);
	//add f0*f1*f2

	for (int i = 0; i < fac0.c - 1; i++) {
		for (int j = 0; j < fac1.c - 1; j++) {
			for (int k = 0; k < fac2.c - 1; k++) {
				if (fac0.ma[in0][i] == 1 && fac1.ma[in1][j] == 1) {
					if (fac2.ma[in2][k] == 1)
					{
						//the term x_i*x_j*x_k
						int i0 = i, j0 = j, k0 = k;//(j0>=i0 is necessary)




						int m;
						if (i0 > j0) {
							m = i0;
							i0 = j0;
							j0 = m;
						}
						if (j0 > k0) {
							m = j0;
							j0 = k0;
							k0 = m;
						}
						if (j0 < i0) {
							m = i0;
							i0 = j0;
							j0 = m;
						}






						int r = j0 - i0;

						int f = k0 - j0;



						if (r == 0)
						{
							if (f > 0)
							{
								int index = (total + (total - (k0 - i0) + 1)) * (k0 - i0) / 2 + i0;
								qeq[row][index] ^= 1;

							}
							else
							{
								int index = i0;
								qeq[row][index] ^= 1;

							}
						}
						else
						{
							if (f == 0)
							{
								int index = (total + (total - (k0 - i0) + 1)) * (k0 - i0) / 2 + i0;
								qeq[row][index] ^= 1;

							}
							else {
								int w = 0;
								for (int i = 0; i < i0; i++)
								{
									w += C(total - 1 - i, 2);
								}
								int index = total + C(total, 2) + w + (total - i0 - 2 + (total - i0 - (k0 - j0) - 1)) * (k0 - j0 - 1) / 2 + (j0 - i0 - 1);

								if (index >= 176954) {
									cout << "i,j,k:" << i << " , " << j << " , " << k << endl;
									cout << "wrong4" << endl;
								}
								if (index < 0) {
									cout << "minus1" << endl;
								}
								qeq[row][index] ^= 1;

							}

						}


					}
					


				}
			}
		}
	}






}


int LowMC::onlineCheck(vector<vector<unsigned long long>>& Dh, M& Q1, M& P0, vector<bool>& ga) {
	//compute beta from gamma
	bool gamma[125], beta[125];
	for (int i = 0; i < 125; i++)
		gamma[i] = ga[i + 3];
	matrixMul(Q1, gamma, beta);

	unsigned long long index = 0,one=1;
	for (int i = 125 - 23; i < 125; i++) {
		index = index | (beta[i] << (i - (125 - 23)));
	}

	/*///////////////////////used for test (may not correct for the current configurations)
	bool ul[40];////39+1=40, u[39] used for the constant bit (episilon)
	for (int i = 0; i < Dh[index].size(); i++) {
		for (int j = 0; j < 39; j++) {
			ul[j] = (Dh[index][i] >> j) & 0x1;
		}

		ul[39] = 1;
		bool ulRes[125];//39+1=40, uP0[39] used for the constant bit (episilon)
		matrixMul(P0, ul, ulRes);

		bool ur[102];//in total 141=39+102 variables
		for (int i = 0; i < 102; i++) {//compute u[40,...,
			ur[i] = beta[i] ^ ulRes[i];
		}
		
		bool check = true;
		bool uv[141] = {
			1,1,0,0,1,1,0,1,0,1,1,0,0,0,0,1,0,1,0,0,1,0,0,0,1,1,1,0,0,0,0,0,0,1,0,1,1,0,1,1,0,1,0,0,1,1,1,1,1,0,1,1,0,1,1,0,0,1,0,0,1,1,0,0,1,1,1,0,0,0,0,0,0,0,1,0,0,1,1,0,1,0,1,0,0,1,1,1,1,0,1,1,0,1,0,1,0,1,1,1,0,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,1,1,0,1,0,1,1,0,1,0,0,0,1,1,0,0,1,0,
		};
		bool g[125] = {
			1,0,0,0,1,1,0,1,1,1,1,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,1,1,1,1,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,1,0,
		};
		for (int i = 0; i < 125; i++) {
			if (g[i] != gamma[i]) {
				check = false;
				break;
			}
		}
		if (check) {
			for (int j = 0; j < 39; j++) {
				if (ul[j] != uv[j]) {
					check = false;
					break;
				}
			}
			for (int j = 0; j < 102; j++) {
				if (ur[j] != uv[j+39]) {
					check = false;
					break;
				}
			}
			if (check) {
				cout << "find the correct one!" << endl;
				for (int j = 0; j < 39; j++)
					cout << ul[j];
				for (int j = 0; j < 102; j++)
					cout << ur[j];
				cout << endl;
				for (int j = 0; j < 141; j++)
					cout << uv[j];
				cout << endl;
			}
		}
	}
	*/////////////////////////////////////////
	
	return Dh[index].size();
}


/********************************
*the optimized key-recovery phase
*********************************/


void LowMC::keyRecovery(bool key[], bool c[], int r, vector<vector<bool> >& LOut, vector<vector<bool> >& SOut, vector<vector<bool> >& sOut, vector<vector<bool> >& lOut,bool y[]) {
	//Round function = S -> L
	int total = 98;//consider the last 81 rounds
	int index = 0;
	vector<vector<bool> > intermediateSOut(total);
	for (int i = 0; i < total; i++) {
		intermediateSOut[i].clear();
		for (int j = 0; j < N; j++)
			intermediateSOut[i].push_back(0);
	}
	bool tmp[N];
	for (int i = 0; i < N; i++)
		tmp[i] = c[i];

	M eqSys;
	eqSys.r = 294;//98*3 (at most 243 linear equations)
	eqSys.c = 177;//128+3*16+1
	clearMatrix(eqSys);

	vector<M> expLOut(total+1);
	for (int i = 0; i < expLOut.size(); i++) {
		expLOut[i].r = N, expLOut[i].c = 177;
		clearMatrix(expLOut[i]);
	}
	for (int i = 0; i < N; i++)
		expLOut[0].ma[i][expLOut[0].c - 1] = c[i];//initialize the constant part
	
	vector<M> expSOut(total+1);
	for (int i = 0; i < expSOut.size(); i++) {
		expSOut[i].r = N, expSOut[i].c = 177;
		clearMatrix(expSOut[i]);
	}

	int cnt = 0;
	eqSys.r = 0;//at first, there is no useful equation.
	//test the correctness of expressions
	bool testVec[177],resVec[177];
	for (int i = 0; i < 177; i++)
		testVec[i] = 0;
	for (int i = 0; i < N; i++) 
		testVec[i] = key[i];
	testVec[176] = 1;
	/////////////////////////////////////

	int freeVars = 0;//the number of free variables after gaussian elimination
	//store the expressions of the intermediate variables
	M extraEq;
	extraEq.r = 48;
	extraEq.c = 177;
	clearMatrix(extraEq);

	for (int i = 0; i < 98; i++) {
		index = r - 1 - i;
		//first, inverse constant addition
		for (int j = 0; j < N; j++)
			expLOut[i].ma[j][expLOut[i].c-1] ^= CONS[index][j];
		//add round key KF[index+1]
		for (int jr = 0; jr < N; jr++) {
			for (int jc = 0; jc < N; jc++)
				expLOut[i].ma[jr][jc] ^= KF[index + 1].ma[jr][jc];
		}
		//inverse L
		matrixMul(IL[index], expLOut[i], expSOut[i]);
		
		//inverse S (use sOut[index],lOut[index-1])
		//check whether the output difference is zero
		int out = sOut[index][0] + 2 * sOut[index][1] + 4 * sOut[index][2];
		int in = lOut[index - 1][0] + 2 * lOut[index - 1][1] + 4 * lOut[index - 1][2];

		//cout << hex << in << " " << out << endl;
		/*///////////check the correctness of expSOut[i]
		matrixMul(expSOut[i], testVec, resVec);
		for (int j = 0; j < 128; j++)
			resVec[j] ^= SOut[index][j];
		outputArray(resVec, 128);
		*////////////////////////

		if (out == 0) {//introduce intermeidate variables
			expLOut[i + 1].ma[0][N + 3 * cnt] = 1;
			expLOut[i + 1].ma[1][N + 3 * cnt + 1] = 1;
			expLOut[i + 1].ma[2][N + 3 * cnt + 2] = 1;
			//update testVector
			testVec[N + 3 * cnt] = LOut[index - 1][0];
			testVec[N + 3 * cnt + 1] = LOut[index - 1][1];
			testVec[N + 3 * cnt + 2] = LOut[index - 1][2];
			///////////////////
			//store the expressions
			for (int jr = 0; jr < 3; jr++) {
				for (int jc = 0; jc < expSOut[i].c; jc++)
					extraEq.ma[3 * cnt + jr][jc] = expSOut[i].ma[jr][jc];
			}
			cnt++;
		}
		else {//extract equations and freely linearize the sbox
			dynamicallyUpdateExpression(expLOut[i + 1], expSOut[i], in,out);
			extractEquations(eqSys, expSOut[i], in, out);
		}

		//copy the remaining expressions
		for (int jr = 3; jr < N; jr++) {
			for (int jc = 0; jc < expSOut[i].c; jc++)
				expLOut[i + 1].ma[jr][jc] = expSOut[i].ma[jr][jc];
		}

		////////////check the correctness of expLOut[i+1]
		matrixMul(expLOut[i+1], testVec, resVec);
		for (int j = 0; j < 128; j++)
			resVec[j] ^= LOut[index-1][j];
		//outputArray(resVec, 128);
		if (resVec[0] != 0 || resVec[1] != 0 || resVec[2] != 0) {
			cout << SOut[index][0] << " " << SOut[index][1] << " " << SOut[index][2] << endl;
			cout << LOut[index-1][0] << " " << LOut[index-1][1] << " " << LOut[index-1][2] << endl;
			//outputM(expSOut[i]);
			//cout << i<<"diff:" << in << " " << out << endl;
			//outputM(expLOut[i + 1]);
			system("pause");
		}
		//////////////////////////////////////////////////the correctness is verified

		////check the correctness of the extract equations
		if (eqSys.r > 0) {
			matrixMul(eqSys, testVec, resVec);
			//outputArray(resVec, eqSys.r);
			if (resVec[eqSys.r - 1] != 0 || resVec[eqSys.r - 2] != 0) {
				system("pause");
			}
		}
		///////the correctness is verified

		//the condition to exit
		if (eqSys.r >= N + 3 * cnt) {//directly solve the system
			cout << "linear:" << eqSys.r << " \t quadratic:" << 0 << endl;
			break;
		}
		
	}
	//outputM(extraEq);
	freeVars = (N + 3 * cnt) - eqSys.r;
	if (freeVars > 0) {
		cout << "freeVars:" << freeVars << endl;
		cout << "row:" << cnt * 3 << endl;
	}
	
	
	bool yy[6];
	for (int i = 0; i < 6; i++)
	{
		yy[i] = y[i];
	}
	
	solveKey(eqSys, extraEq, cnt * 3, testVec, key,yy);

	//system("pause");
	//cout << "the size of the constructed equation system:" << eqSys.r << endl;

	//gauss(eqSys, cnt * 3 + 128);
	//outputM(eqSys);
	//system("pause");
	//outputM(expLOut[81]);
	//system("pause");
}

void LowMC::solveKey(M& eqSys, M& extraEq, int extraSize, bool testVec[], bool key[],bool yy[]) {
	/*cout << "test" << endl;
	
	for (int i = 0; i < N + extraSize; i++) {
		cout << testVec[i];
	}
	cout << endl;
	cout << "eqSys=" << endl;
	outputM(eqSys);
	cout << endl;*/
	gauss(eqSys, extraSize + 128);
	//outputM(eqSys);
	cout << "further simplified:" << endl;
	simplify(eqSys, extraSize +128);
	//outputM(eqSys);
	if (eqSys.r >= N + extraSize)
	{//directly solve the system
		cout << "directly";
		return;
	}
	if (eqSys.r < N + extraSize)
	{


		cout << "check:";
		bool res[177];
		matrixMul(eqSys, testVec, res);
		for (int i = 0; i < eqSys.r; i++)
			cout << res[i];
		/*cout << endl;
		cout << "eqSys=" << endl;
		outputM(eqSys);
		cout << endl;*/
		//mark the free variables
		int totalVars = extraSize + 128;
		vector<bool> freeVar(totalVars);
		vector<int> index(totalVars);
		for (int i = 0; i < totalVars; i++)
			index[i] = 0;
		for (int i = 0; i < totalVars; i++)
			freeVar[i] = 1;
		for (int i = 0; i < eqSys.r; i++) {
			for (int j = i; j < eqSys.c - 1; j++) {
				if (eqSys.ma[i][j] == 1) {
					freeVar[j] = 0;
					index[j] = i;//record the expression for the variable u_j, i.e. the i-th row
					break;
				}
			}
		}
		/*vector<bool> zz(totalVars);
		cout << "zz=" << endl;
		for (int i = 0; i < totalVars; i++)
		{zz[i] = 0;
		
			if (freeVar[i]) {
				zz[i] = 1;
			}
			cout << zz[i] ;
		}
		cout << endl;*/
		int freeVarCnt = 0;
		for (int i = 0; i < freeVar.size(); i++) {
			if (freeVar[i])
				freeVarCnt++;
		}
		cout << "the number of free variables:" << freeVarCnt << " \t #terms:" << (freeVarCnt + (freeVarCnt) * (freeVarCnt - 1) / 2) << endl;

		//update extraEq
		for (int i = 0; i < extraSize; i++) {
			for (int j = 0; j < extraEq.c - 1; j++) {
				if (extraEq.ma[i][j] == 1 && freeVar[j] == 0) {
					extraEq.ma[i][j] = 0;//update it
					for (int k = j + 1; k < extraEq.c; k++) {
						extraEq.ma[i][k] = extraEq.ma[i][k] ^ eqSys.ma[index[j]][k];
					}
				}
			}
		}

		//outputM(extraEq);
		/*matrixMul(extraEq, testVec, res);
		bool t[3];
		for (int j = 0; j < extraSize / 3; j++) {
			t[0] = testVec[128+3 * j] ^ (testVec[128+1 + 3 * j] & testVec[128+2 + 3 * j]);
			t[1] = testVec[128+3 * j] ^ testVec[128+1 + 3 * j] ^ (testVec[128+3 * j] & testVec[128+2 + 3 * j]);
			t[2] = testVec[128+3 * j] ^ testVec[128+1 + 3 * j] ^ testVec[128+2 + 3 * j] ^ (testVec[128+3 * j] & testVec[128+1 + 3 * j]);
			cout << t[0] << t[1] << t[2];
		}
		cout << endl;
		outputArray(res, extraSize);*/
		///the correctness is verified

		//rename variables
		vector<int> mapIndex(totalVars), inverseMap(totalVars);
		int rvar = 0;
		for (int i = 0; i < totalVars; i++) {
			if (freeVar[i]) {
				mapIndex[i] = rvar;
				inverseMap[rvar] = i;
				rvar++;
			}
		}

		M left, right;
		left.r = extraSize, right.r = extraSize;
		left.c = freeVarCnt + 1, right.c = freeVarCnt + 1;
		clearMatrix(left), clearMatrix(right);

		bool* checkVec = new bool[freeVarCnt + 1];
		for (int i = 0; i < freeVarCnt; i++) {
			checkVec[i] = testVec[inverseMap[i]];
			
		}
		checkVec[freeVarCnt] = 1;

		for (int i = 0; i < extraSize; i++) {
			if (freeVar[128 + i]) {//it is a free variables
				left.ma[i][mapIndex[128 + i]] = 1;
				left.ma[i][left.c - 1] = 0;
			}
			else {//it is not a free variable, get the corresponding expression
				for (int j = 128 + i + 1; j < eqSys.c - 1; j++) {
					if (eqSys.ma[index[128 + i]][j] == 1) {
						left.ma[i][mapIndex[j]] = 1;
						//cout << j << " " << mapIndex[j] << endl;
					}
				}
				left.ma[i][left.c - 1] = eqSys.ma[index[128 + i]][eqSys.c - 1];
			}
		}
		//cout << "left:" << endl;
		//outputM(left);//test is passed, left is correctly constructed

		//construct right
		for (int i = 0; i < extraSize; i++) {
			for (int j = 0; j < extraEq.c - 1; j++) {
				if (extraEq.ma[i][j] == 1) {
					right.ma[i][mapIndex[j]] = 1;
				}
			}
			right.ma[i][right.c - 1] = extraEq.ma[i][extraEq.c - 1];
		}
		//cout << "right:" << endl;
		//outputM(right);//test is passed, left is correctly constructed

		//construct the quadratic equation system with left and right
		int quTerms = freeVarCnt + (freeVarCnt * (freeVarCnt - 1) / 2);
		bool* quVec = new bool[quTerms + 1];
		for (int i = 0; i < freeVarCnt; i++) {
			for (int j = i; j < freeVarCnt; j++) {
				int k = (freeVarCnt + (freeVarCnt - (j - i) + 1)) * (j - i) / 2 + i;
				if (k >= quTerms) {
					cout << "wrong5" << endl;
					system("pause");
				}
				quVec[k] = checkVec[i] & checkVec[j];
				//cout << checkVec[i] << checkVec[j] << quVec[k] << " ";
			}
		}
		//cout << endl;
		quVec[quTerms] = 1;
		/*cout << "queVec" << endl;
		for (int i = 0; i < quTerms; i++) {
			cout << quVec[i];
		}*/
		//cout << endl;
		bool quVecRes[300];
		bool* quu = new bool[22];
		for (int i = 0; i < 6; i++) {
			for (int j = i+1; j < 6; j++) {
				int k = (6 + (6 - (j - i) + 1)) * (j - i) / 2 + i;
				
				quu[k-6] = checkVec[i] & checkVec[j];
				//cout << checkVec[i] << checkVec[j] << quVec[k] << " ";
			}
		}
		for (int i = 0; i < 6; i++)
		{
			quu[i + 15] = checkVec[i];
		}
		quu[21] = 1;
		//construct quadratic equations
		M quadratic;
		quadratic.r = 2 * 14;
		quadratic.c = quTerms + 1;
		clearMatrix(quadratic);

		//cout << quadratic.r << " " << quadratic.c << endl;
		//cout << "quadratic:" << endl;
		//outputM(quadratic);
		//cout << "updated:" << endl;

		int cnt = 2;
		for (int i = 0; i < cnt; i++) {
			//left.ma[3*i], ma[3*i+1], ma[3*i+2]
			//right.ma[3*i], ma[3*i+1], ma[3*i+2]
			int j = 3 * i;
			int k = 14 * i;

			addLinear(quadratic, k, left, j);
			addLinear(quadratic, k, right, j);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k+1);
			k++;

			addLinear(quadratic, k, left, j);
			addLinear(quadratic, k, left, j + 1);
			addLinear(quadratic, k, right, j + 1);
			addQuadratic(quadratic, k, left, j, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addLinear(quadratic, k, left, j);
			addLinear(quadratic, k, left, j + 1);
			addLinear(quadratic, k, left, j + 2);
			addLinear(quadratic, k, right, j + 2);
			addQuadratic(quadratic, k, left, j, left, j + 1, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addLinear(quadratic, k, right, j);
			addLinear(quadratic, k, right, j + 1);
			addLinear(quadratic, k, left, j);
			addQuadratic(quadratic, k, right, j + 1, right, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addLinear(quadratic, k, right, j + 1);
			addLinear(quadratic, k, left, j + 1);
			addQuadratic(quadratic, k, right, j, right, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addLinear(quadratic, k, right, j);
			addLinear(quadratic, k, right, j + 1);
			addLinear(quadratic, k, right, j + 2);
			addLinear(quadratic, k, left, j + 2);
			addQuadratic(quadratic, k, right, j, right, j + 1, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j, left, j + 1, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 1, freeVarCnt);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j, left, j + 2, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 2, freeVarCnt);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j + 1, left, j, freeVarCnt);
			addLinear(quadratic, k, left, j);
			addQuadratic(quadratic, k, left, j, left, j + 1, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j + 1, left, j + 2, freeVarCnt);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			//system("pause");
			//eq11,12,13,14
			addQuadratic(quadratic, k, right, j + 2, left, j, freeVarCnt);
			addLinear(quadratic, k, left, j);
			addQuadratic(quadratic, k, left, j, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j + 2, left, j + 1, freeVarCnt);
			addLinear(quadratic, k, left, j + 1);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j, left, j, freeVarCnt);
			addLinear(quadratic, k, left, j);
			addQuadratic(quadratic, k, right, j + 1, left, j + 1, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 1, freeVarCnt);
			addLinear(quadratic, k, left, j + 1);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;

			addQuadratic(quadratic, k, right, j + 1, left, j + 1, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 1, freeVarCnt);
			addLinear(quadratic, k, left, j + 1);
			addQuadratic(quadratic, k, right, j + 2, left, j + 2, freeVarCnt);
			addQuadratic(quadratic, k, left, j, left, j + 2, freeVarCnt);
			addQuadratic(quadratic, k, left, j + 1, left, j + 2, freeVarCnt);
			addLinear(quadratic, k, left, j + 2);
			//matrixMul(quadratic, quVec, quVecRes);
			//cout << "index:" << k - 14 * i << ": ";
			//outputArray(quVecRes, k + 1);
			k++;
		}

		//matrixMul(quadratic, quVec, quVecRes);
		//for (int i = 0; i < quadratic.c; i++) {
		//	if (quVecRes[i] != 0) {
		//		cout << "wrong6" << endl;
		//		system("pause");
		//	}
		//}
		//cout << "quadratic=" << endl;
		//outputM(quadratic);
		//cout << endl;
		M Updatequadratic;
		Updatequadratic.r = 2 * 14;
		Updatequadratic.c = quTerms + 1;
		//x0*x1--x0*x5
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 4; j++)
			{
				Updatequadratic.ma[i][j] = quadratic.ma[i][12 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 3; j++)
			{
				Updatequadratic.ma[i][j + 5] = quadratic.ma[i][23 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 2; j++)
			{
				Updatequadratic.ma[i][j + 9] = quadratic.ma[i][33 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 1; j++)
			{
				Updatequadratic.ma[i][j + 12] = quadratic.ma[i][42 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 0; j++)
			{
				Updatequadratic.ma[i][j + 14] = quadratic.ma[i][50 + j];
			}
		}
		//l(y)*x0
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w0 = 50;
			for (int j = 7; j > 1; j--)
			{
				
				
				w0 = j + w0;
					Updatequadratic.ma[i][15+7-j] = quadratic.ma[i][w0];
				

			}
		}
		//l(y)*x1
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w1 = 43;
			for (int j = 8; j > 2; j--)
			{
				

				w1 = j + w1;
					Updatequadratic.ma[i][8-j + 21] = quadratic.ma[i][w1];
				

			}
		}
		//l(y)*x2
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w2 = 35;
			for (int j = 9; j > 3; j--)
			{
				

				w2 = j + w2;
					Updatequadratic.ma[i][9-j + 27] = quadratic.ma[i][w2];
				

			}
		}
		//l(y)*x3
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w3 = 26;
			for (int j = 10; j > 4; j--)
			{
				

				w3 = j + w3;
					Updatequadratic.ma[i][10-j + 33] = quadratic.ma[i][w3];
				

			}
		}
		//l(y)*x4
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w4 = 16;
			for (int j = 11; j > 5; j--)
			{
				

				w4 = j + w4;
					Updatequadratic.ma[i][11-j + 39] = quadratic.ma[i][w4];
				

			}
		}
		//l(y)*x5
		
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			int w5 = 5;
			for (int j = 12; j > 5; j--)
			{
				

				w5 = j + w5;
					Updatequadratic.ma[i][12-j + 45] = quadratic.ma[i][w5];
				

			}
		}
		//x0--x5
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 5; j++)
			{
				Updatequadratic.ma[i][j + 51] = quadratic.ma[i][j];
			}
		}
		//x6x7--x6x11
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 4; j++)
			{
				Updatequadratic.ma[i][j + 57] = quadratic.ma[i][18 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 3; j++)
			{
				Updatequadratic.ma[i][j + 62] = quadratic.ma[i][29 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 2; j++)
			{
				Updatequadratic.ma[i][j + 66] = quadratic.ma[i][39 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 1; j++)
			{
				Updatequadratic.ma[i][j + 69] = quadratic.ma[i][48 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 0; j++)
			{
				Updatequadratic.ma[i][j + 71] = quadratic.ma[i][56 + j];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{
			for (int j = 0; j <= 5; j++)
			{
				Updatequadratic.ma[i][j + 72] = quadratic.ma[i][j + 6];
			}
		}
		for (int i = 0; i < Updatequadratic.r; i++)
		{

			Updatequadratic.ma[i][Updatequadratic.c - 1] = quadratic.ma[i][Updatequadratic.c - 1];

		}
		//cout << "Updatequadratic=" << endl;
		//outputM(Updatequadratic);
		//cout << endl;
		//Adjust the order to fit the crossbred algorithm
		M colExQuadratic;
		colExQuadratic.r = Updatequadratic.r;
		colExQuadratic.c = Updatequadratic.c;
		clearMatrix(colExQuadratic);
		for (int i = 0; i < 6; i++)
		{
			cout << yy[i];
		}
		cout << endl;
		for (int i = 0; i < Updatequadratic.r; i++) {
			for (int j = 0; j < 15; j++) {
				colExQuadratic.ma[i][j] = Updatequadratic.ma[i][j];
			}
			colExQuadratic.ma[i][colExQuadratic.c - 1] = Updatequadratic.ma[i][colExQuadratic.c - 1];
		}
		for (int i = 0; i < Updatequadratic.r; i++) {
			for (int j = 0; j < 6; j++) {
				colExQuadratic.ma[i][51+j] = Updatequadratic.ma[i][51+j];
			}
		}
		
		for (int k = 0; k < Updatequadratic.r; k++) {
			for (int i = 0; i < 6; i++) {
				for (int j = 0; j < 6; j++) {
					
					if (yy[j] == 1 )
					{
						if (Updatequadratic.ma[k][15 + i * 6 + j] == 1) {
							colExQuadratic.ma[k][15 + i * 6 + j] = 1;
						}
						
					}
					else {
						colExQuadratic.ma[k][15 + i * 6 + j] = 0;
					}
				}
			}
		}
		
		for (int k = 0; k < Updatequadratic.r; k++) {
			for (int i = 0; i < 6; i++) {
				if (yy[i] == 1&& Updatequadratic.ma[k][72 + i] == 1)
				{
					colExQuadratic.ma[k][72 + i] = 1;
				}
			}
			
		}
	
		for (int k = 0; k < Updatequadratic.r; k++) {
			for (int i = 0; i < 6; i++) {
				for (int j = i+1; j <6; j++) {
					int s = 0;
					s = (6 + (6 - (j - i) + 1)) * (j - i) / 2 + i-6+ 57;				
					if (yy[i] == 1&& yy[j] == 1)
					{				
							if (Updatequadratic.ma[k][s] == 1) {
								colExQuadratic.ma[k][s] = 1;
							}											
					}
				 
				}
			}
		}
		//cout << "colExQuadratic=" << endl;
		//outputM(colExQuadratic);
		//cout << endl;
		
		M col;
		col.r = colExQuadratic.r;
		col.c = 15 + colExQuadratic.r;
		clearMatrix(col);
		for (int i = 0; i < colExQuadratic.r; i++) {
			for (int j = 0; j < 15; j++) {
				col.ma[i][j] = colExQuadratic.ma[i][j];
			}
			col.ma[i][15 + i] = 1;
		}
		
		gauss(col, col.c);
		simplify(col, col.c);
		//cout << "col=" << endl;
		//outputM(col);
		//cout << endl;
		M pp;
		pp.r = col.r;
		pp.c = col.r;
		 clearMatrix(pp);
		for (int i = 0; i < col.r; i++) {
			
			for (int j = 0; j < col.r; j++) {
				pp.ma[i][j] = col.ma[i][j + 15];
			}
		}
		//cout << "pp=" << endl;
		//outputM(pp);
		//cout << endl;
		M colExQuadratic1;
		colExQuadratic1.r = 28;
		colExQuadratic1.c = 22;
		for (int i = 0; i < colExQuadratic1.r; i++) {

			
				int z = 0;
				for (int j = 0; j < 6; j++) {
					z =z^ colExQuadratic.ma[i][15 + j ];
					
				}			
				colExQuadratic1.ma[i][15] = z^ colExQuadratic.ma[i][51 ];
			
		}
		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 0; j < 6; j++) {
				z = z ^ colExQuadratic.ma[i][21 + j];

			}
			colExQuadratic1.ma[i][16] = z ^ colExQuadratic.ma[i][52];

		}
		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 0; j < 6; j++) {
				z = z ^ colExQuadratic.ma[i][27 + j];

			}
			colExQuadratic1.ma[i][17] = z ^ colExQuadratic.ma[i][53];

		}
		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 0; j < 6; j++) {
				z = z ^ colExQuadratic.ma[i][33 + j];

			}
			colExQuadratic1.ma[i][18] = z ^ colExQuadratic.ma[i][54];

		}
		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 0; j < 6; j++) {
				z = z ^ colExQuadratic.ma[i][39 + j];

			}
			colExQuadratic1.ma[i][19] = z ^ colExQuadratic.ma[i][55];

		}
		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 0; j < 6; j++) {
				z = z ^ colExQuadratic.ma[i][45 + j];

			}
			colExQuadratic1.ma[i][20] = z ^ colExQuadratic.ma[i][56];

		}
	

		for (int i = 0; i < colExQuadratic1.r; i++) {


			int z = 0;
			for (int j = 57; j < colExQuadratic.c; j++) {
				z =z^ colExQuadratic.ma[i][j];
			}

			
			colExQuadratic1.ma[i][21] = z;

		}
		for (int i = 0; i < colExQuadratic1.r; i++) {



			for (int j = 0; j < 15; j++) {
				colExQuadratic1.ma[i][j] = colExQuadratic.ma[i][j];
			}
		}
		//test have pasted
		/*
		
		matrixMul(colExQuadratic1, quu, quVecRes);
		cout << "quVecRes=" << endl;
		for (int i = 0; i < 22; i++)
		{
			cout << quVecRes[i] ;
		}
		cout << endl;*/
		//cout << "colExQuadratic1=" << endl;
		//outputM(colExQuadratic1);
		//cout << endl;
		
		M qq;
		qq.r = colExQuadratic1.r;
		qq.c = 7;
		for (int i = 0; i < colExQuadratic1.r; i++) {
			for (int j = 0; j < 7; j++) {
				qq.ma[i][j] = colExQuadratic1.ma[i][j + 15];
			}
		}
		matrixMul(pp, qq);
		//cout << "qq=" << endl;
		//outputM(qq);
		cout << endl;
		
		//cout << "solve last 6 variables" << endl;
		M solve;
		solve.r = 13;
		solve.c = 7;
		for (int i = 0; i < 13; i++) {
			for (int j = 0; j < 7; j++) {
				solve.ma[i][j] = qq.ma[15 + i][j];
			}
		}
		
		
		//cout << "solve=" << endl;
		//outputM(solve);
		//cout << endl;
		gauss(solve, solve.c );
		
		//cout << "solve=" << endl;
		//outputM(solve);
		//cout << endl;
		vector<vector<bool> > sol;
		int solNum = 0;
		
		storeSolutions(sol, solve, solNum);
		cout << "solNum="<< solNum << endl;
		/*
		
		cout << "checkVec=" << endl;
		for (int i = 0; i < 12; i++) {
			cout << checkVec[i];
		}
		cout << endl;
		*/
		
		
		
		for (int i = 0; i < solNum; i++) {
			bool findKey = true;
			for (int j = 0; j < 6; j++) {
				cout << sol[i][j];
				if (sol[i][j] != checkVec[j]) {
					
					findKey = false;
				}
					
			}
			cout << endl;
			if (findKey)
				cout << "sol" << i << " : correct" << endl;
			else
				cout << "sol" << i << " :wrong" << endl;
			//outputArray(checkVec, freeVarCnt);
		}
		
		cout << "solve end" << endl;
		cout << endl;
		
		delete[]checkVec;
		delete[]quVec;
		//system("pause");
	}
}

void LowMC::addLinear(M& qeq, int row, M& lin, int index) {
	for (int i = 0; i < lin.c-1; i++) {//variable part
		qeq.ma[row][i] ^= lin.ma[index][i];
	}
	qeq.ma[row][qeq.c - 1] ^= lin.ma[index][lin.c - 1];//constant part
}

void LowMC::addQuadratic(M& qeq, int row, M& fac0, int in0, M& fac1, int in1, int total) {
	//(f0+a) & (f1+b) = f0f1 + b*f0 + a*f1 + ab
	if (fac0.ma[in0][fac0.c - 1]) {//a=1, add f1
		for (int i = 0; i < fac1.c - 1; i++) {//variable part
			qeq.ma[row][i] ^= fac1.ma[in1][i];
		}
	}
	
	if (fac1.ma[in1][fac1.c - 1]) {
		for (int i = 0; i < fac0.c - 1; i++) {//variable part
			qeq.ma[row][i] ^= fac0.ma[in0][i];
		}
	}

	qeq.ma[row][qeq.c - 1] = qeq.ma[row][qeq.c - 1] ^ (fac0.ma[in0][fac0.c - 1] & fac1.ma[in1][fac1.c - 1]);

	//add f0*f1
	for (int i = 0; i < fac0.c - 1; i++) {
		for (int j = 0; j < fac1.c - 1; j++) {
			if (fac0.ma[in0][i] == 1 && fac1.ma[in1][j] == 1) {
				//the term x_i*x_j
				int i0 = i, j0 = j;//(j0>=i0 is necessary)
				if (i0 > j0) {
					int t = i0;
					i0 = j0;
					j0 = t;
				}
				int index = (total + (total - (j0 - i0) + 1)) * (j0 - i0) / 2 + i0;
				if (index >= qeq.c) {
					cout << "i,j:" << i << " , " << j << endl;
					cout << "wrong8" << endl;
				}
				if (index < 0) {
					cout << "minus" << endl;
				}
				qeq.ma[row][index] ^= 1;
			}
		}
	}
}

void LowMC::dynamicallyUpdateExpression(M& expLOut, M& expSOut, int in, int out) {
	bool c[3];
	vector<vector<int> > add(3);
	for (int i = 0; i < 3; i++)
		add[i].clear();

	//input diff : x0x1x2: 100
	if (in == 1 && out == 1) {
		//x0=z0+1, x1=1, x2=1, 
		c[0] = 1, c[1] = 1, c[2] = 1;
		add[0].push_back(0);
	}
	else if (in == 1 && out == 5) {
		//x0=z0,x1=0,x2=1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[0].push_back(0);
	}
	else if (in == 1 && out == 3) {
		//x0=z0,x1=1,x2=0
		c[0] = 0, c[1] = 1, c[2] = 0;
		add[0].push_back(0);
	}
	else if (in == 1 && out == 7) {
		//x0=z0,x1=0,x2=0,
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[0].push_back(0);
	}

	//input diff : x0x1x2: 010
	else if (in == 2 && out == 2) {
		//x0=1,x1=z1+1,x2=0
		c[0] = 1, c[1] = 1, c[2] = 0;
		add[1].push_back(1);
	}
	else if (in == 2 && out == 6) {
		//x0=0,x1=z1,x2=0
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[1].push_back(1);
	}
	else if (in == 2 && out == 3) {
		//x0=1,x1=z1,x2=1
		c[0] = 1, c[1] = 0, c[2] = 1;
		add[1].push_back(1);
	}
	else if (in == 2 && out == 7) {
		//x0=0,x1=z1,x2=1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[1].push_back(1);
	}

	//input diff: x0x1x2: 110
	else if (in == 3 && out == 2) {
		//x0=x1+1, x1=z1, x2=1
		c[0] = 1, c[1] = 0, c[2] = 1;
		add[0].push_back(1), add[1].push_back(1);
	}
	else if (in == 3 && out == 6) {
		//x0=x1, x1=z1, x2=1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[0].push_back(1), add[1].push_back(1);
	}
	else if (in == 3 && out == 1) {
		//x0=x1+1=z0, x1=z0+1, x2=0
		c[0] = 0, c[1] = 1, c[2] = 0;
		add[0].push_back(0), add[1].push_back(0);
	}
	else if (in == 3 && out == 5) {
		//x0=x1, x1=z0, x2=0
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[0].push_back(0), add[1].push_back(0);
	}

	//input diff: x0x1x2: 001
	else if (in == 4 && out == 4) {
		//x0=0, x1=0, x2=z2
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[2].push_back(2);
	}
	else if (in == 4 && out == 6) {
		//x0=1, x1=0, x2=z2+1
		c[0] = 1, c[1] = 0, c[2] = 1;
		add[2].push_back(2);
	}
	else if (in == 4 && out == 5) {
		//x0=0, x1=1, x2=z2+1
		c[0] = 0, c[1] = 1, c[2] = 1;
		add[2].push_back(2);
	}
	else if (in == 4 && out == 7) {
		//x0=1, x1=1, x2=z2+1
		c[0] = 1, c[1] = 1, c[2] = 1;
		add[2].push_back(2);
	}

	//input diff: x0x1x2: 101
	else if (in == 5 && out == 4) {
		//x0=x2=z2+1, x1=1, x2=z2+1
		c[0] = 1, c[1] = 1, c[2] = 1;
		add[0].push_back(2), add[2].push_back(2);
	}
	else if (in == 5 && out == 1) {
		//x0=x2=z0, x1=0, x2=z0
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[0].push_back(0), add[2].push_back(0);
	}
	else if (in == 5 && out == 6) {
		//x0=x2+1=z1+1, x1=1, x2=z1
		c[0] = 1, c[1] = 1, c[2] = 0;
		add[0].push_back(1), add[2].push_back(1);
	}
	else if (in == 5 && out == 3) {
		//x0=x2+1=z1, x1=0, x2=z1+1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[0].push_back(1), add[2].push_back(1);
	}

	//input diff: x0x1x2: 011
	else if (in == 6 && out == 4) {
		//x0=1, x1=x2+1, x1=z2 -> x2=z2+1
		c[0] = 1, c[1] = 0, c[2] = 1;
		add[1].push_back(2), add[2].push_back(2);
	}
	else if (in == 6 && out == 2) {
		//x0=0, x1=x2+1, x1=z1 -> x2=z1+1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[1].push_back(1), add[2].push_back(1);
	}
	else if (in == 6 && out == 5) {
		//x0=1, x1=x2, x1=z0+1 -> x2=z0+1
		c[0] = 1, c[1] = 1, c[2] = 1;
		add[1].push_back(0), add[2].push_back(0);
	}
	else if (in == 6 && out == 3) {
		//x0=0, x1=x2, x1=z0 -> x2=z0
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[1].push_back(0), add[2].push_back(0);
	}

	//input diff: x0x1x2: 111
	else if (in == 7 && out == 4) {
		//x0=z2, x1=x0+1=z2+1, x2=x0+1=z2+1
		c[0] = 0, c[1] = 1, c[2] = 1;
		add[0].push_back(2), add[1].push_back(2), add[2].push_back(2);
	}
	else if (in == 7 && out == 2) {
		//x0=z1, x1=x0=z1, x2=x0=z1
		c[0] = 0, c[1] = 0, c[2] = 0;
		add[0].push_back(1), add[1].push_back(1), add[2].push_back(1);
	}
	else if (in == 7 && out == 1) {
		//x0=z0, x1=x0=z0, x2=x0+1=z0+1
		c[0] = 0, c[1] = 0, c[2] = 1;
		add[0].push_back(0), add[1].push_back(0), add[2].push_back(0);
	}
	else if (in == 7 && out == 7) {
		//x0=z0, x1=x0+1=z0+1, x2=x0=z0
		c[0] = 0, c[1] = 1, c[2] = 0;
		add[0].push_back(0), add[1].push_back(0), add[2].push_back(0);
	}

	for (int i = 0; i < 3; i++) {
		for (int j = 0; j < expLOut.c; j++)//clear
			expLOut.ma[i][j] = 0;
		//assign c to the constant part
		expLOut.ma[i][expLOut.c - 1] = c[i];
		//add row (add[i][0]) of expSOut to expLOut
		if (add[i].size() > 0) {
			for (int j = 0; j < expSOut.c; j++)
				expLOut.ma[i][j] ^= expSOut.ma[add[i][0]][j];
		}
	}
}

void LowMC::extractEquations(M& eq, M& expSOut, int in, int out) {
	bool c[2] = { 0,0 };
	vector<vector<int> > add(2);
	add[0].clear(), add[1].clear();

	//input diff : x0x1x2: 100
	if (in == 1 && out == 1) {
		//z1=1, z2=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(1), add[1].push_back(2);
	}
	else if (in == 1 && out == 5) {
		//z1=0, z0+z2=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(1), add[1].push_back(0), add[1].push_back(2);
	}
	else if (in == 1 && out == 3) {
		//z2=1, z0+z1=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(2);
		add[1].push_back(0), add[1].push_back(1);
	}
	else if (in == 1 && out == 7) {
		//z0=z1, z0=z2
		c[0] = 0, c[1] = 0;
		add[0].push_back(0), add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}

	//input diff : x0x1x2: 010
	else if (in == 2 && out == 2) {
		//z0=1, z2=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(2);
	}
	else if (in == 2 && out == 6) {
		//z0=0, z1=z2
		c[0] = 0, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(1), add[1].push_back(2);
	}
	else if (in == 2 && out == 3) {
		//z2=0,z0+z1=1
		c[0] =0, c[1] = 1;
		add[0].push_back(2);
		add[1].push_back(0), add[1].push_back(1);
	}
	else if (in == 2 && out == 7) {
		//z0+z1=0, z0+z2=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(0), add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}

	//input diff: x0x1x2: 110
	else if (in == 3 && out == 2) {
		//z0=1, z2=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(2);
	}
	else if (in == 3 && out == 6) {
		//z0=0, z1+z2=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(1), add[1].push_back(2);
	}
	else if (in == 3 && out == 1) {
		//z1=1, z2=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(1); 
		add[1].push_back(2);
	}
	else if (in == 3 && out == 5) {
		//z1=0, z0+z2=0
		c[0] = 0, c[1] = 0;
		add[0].push_back(1); 
		add[1].push_back(0),add[1].push_back(2);
	}

	//input diff: x0x1x2: 001
	else if (in == 4 && out == 4) {
		//z0=0, z1=0
		c[0] = 0, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(1);
	}
	else if (in == 4 && out == 6) {
		//z0=1, z1+z2=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(1), add[1].push_back(2);
	}
	else if (in == 4 && out == 5) {
		//z1=1, z0+z2=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}
	else if (in == 4 && out == 7) {
		//z0+z1=1, z0+z2=0;
		c[0] = 1, c[1] = 0;
		add[0].push_back(0), add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}

	//input diff: x0x1x2: 101
	else if (in == 5 && out == 4) {
		//z0=0,z1=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(1);
	}
	else if (in == 5 && out == 1) {
		//z1=0, z2=0
		c[0] = 0, c[1] = 0;
		add[0].push_back(1);
		add[1].push_back(2);
	}
	else if (in == 5 && out == 6) {
		//z0=1, z1+z2=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(1), add[1].push_back(2);
	}
	else if (in == 5 && out == 3) {
		//z2=1, z0+z1=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(2);
		add[1].push_back(0), add[1].push_back(1);
	}

	//input diff: x0x1x2: 011
	else if (in == 6 && out == 4) {
		//z0=1,z1=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(1);
	}
	else if (in == 6 && out == 2) {
		//z0=0, z2=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(2);
	}
	else if (in == 6 && out == 5) {
		//z1=1, z0+z2=0
		c[0] = 1, c[1] = 0;
		add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}
	else if (in == 6 && out == 3) {
		//z2=0, z0+z1=0
		c[0] = 0, c[1] = 0;
		add[0].push_back(2);
		add[1].push_back(0), add[1].push_back(1);
	}

	//input diff: x0x1x2: 111
	else if (in == 7 && out == 4) {
		//z0=1,z1=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(0);
		add[1].push_back(1);
	}
	else if (in == 7 && out == 2) {
		//z0=0,z2=0
		c[0] = 0, c[1] = 0;
		add[0].push_back(0);
		add[1].push_back(2);
	}
	else if (in == 7 && out == 1) {
		//z1=0,z2=1
		c[0] = 0, c[1] = 1;
		add[0].push_back(1);
		add[1].push_back(2);
	}
	else if (in == 7 && out == 7) {
		//z0+z1=1, z0+z2=1
		c[0] = 1, c[1] = 1;
		add[0].push_back(0), add[0].push_back(1);
		add[1].push_back(0), add[1].push_back(2);
	}

	//add to eq
	for (int i = 0; i < 2; i++) {
		for (int j = 0; j < add[i].size(); j++) {
			for (int k = 0; k < expSOut.c; k++)
				eq.ma[eq.r][k] ^= expSOut.ma[add[i][j]][k];
		}
		eq.ma[eq.r][eq.c - 1] = eq.ma[eq.r][eq.c - 1] ^ c[i];
		eq.r++;//increase the number of eqs
	}
}


/*****************************
*
*algebraic equations for DDT
*
*****************************/

void LowMC::searchAlgebraicEquations() {
	//compute DDT
	int t = 64;//6 bits, x0,x1,x2,x3,x4,x5
	bool x[64][6];
	bool valid[64] = { 0 };
	valid[0] = 1;
	for (int i = 0; i < t; i++) {
		for (int j = 0; j < 6; j++) {
			x[i][j] = (i >> j) & 0x1;
		}
		if ((x[i][0] != 0 || x[i][1] != 0 || x[i][2] != 0)&&
			(x[i][3] != 0 || x[i][4] != 0 || x[i][5] != 0)) {
			bool sum = (x[i][0] & x[i][3]) ^ (x[i][1] & x[i][4]) ^ (x[i][2] & x[i][5]);
			if (sum == 1) {
				valid[i] = 1;
			}
		}
	}

	//compute DDT from the definition
	//x[3]=x[0]+x[1]x[2]
	//x[4]=x[0]+x[1]+x[0]x[2]
	//x[5]=x[0]+x[1]+x[2]+x[0]x[1]
	bool y[6], yp[6];
	for (int i = 0; i < 8; i++) {
		for (int j = 0; j < 8; j++) {
			for (int z = 0; z < 8; z++) {
				for (int u = 0; u < 3; u++) {
					y[u] = (z >> u) & 0x1;
					yp[u] = y[u] ^ ((i >> u) & 0x1);
				}
				y[3] = y[0] ^ (y[1] & y[2]);
				y[4] = y[0] ^ y[1] ^ (y[0] & y[2]);
				y[5] = y[0] ^ y[1] ^ y[2] ^ (y[0] & y[1]);

				yp[3] = yp[0] ^ (yp[1] & yp[2])^y[3];
				yp[4] = yp[0] ^ yp[1] ^ (yp[0] & yp[2])^y[4];
				yp[5] = yp[0] ^ yp[1] ^ yp[2] ^ (yp[0] & yp[1])^y[5];

				int out = yp[3] + 2 * yp[4] + 4 * yp[5];
				if (j == out) {
					cout << i << " -> " << yp[3] << " " << yp[4] << " " << yp[5] << endl;
					if (valid[i * 8 + j] == 0) {
						cout << "wrong9" << endl;
					}
					break;
				}
			}
		}
	}

	system("pause");

	//find quadratic equations, we have 6+15+1=22 variables (64 equations)
	M q;
	q.r = 64, q.c = 22;
	clearMatrix(q);
	//outputM(q);

	int c = 0;
	for (int i = 0; i < t; i++)
		q.ma[i][q.c - 1] = 0;//guess the constant

	for (int i = 0; i < t; i++) {
		if (valid[i]) {
			computeQuadraticEq(x[i], q.ma[c]);
			c++;
			//q.ma[i][q.c - 1] = 0;
		}
		else {
			//if ((x[i][0] != 0 || x[i][1] != 0 || x[i][2] != 0) &&
				//(x[i][3] != 0 || x[i][4] != 0 || x[i][5] != 0)) {
				computeQuadraticEq(x[i], q.ma[c]);
				q.ma[c][q.c - 1] ^= 1;
				c++;
			//}
		}
	}
	cout <<"c:"<< c << endl;
	outputM(q);
	cout << "after gauss" << endl;
	gauss(q, q.c - 1);
	outputM(q);
	cout << "simplify:" << endl;
	simplify(q, q.c - 1);
	outputM(q);

	//find cubic equations, we have 6+15+20+1=42 variables (64 equations)
	q.r = 64, q.c = 42;
	clearMatrix(q);
	c = 0;
	for (int i = 0; i < t; i++)
		q.ma[i][q.c - 1] = 0;//guess the constant
	for (int i = 0; i < t; i++) {
		if (valid[i]) {
			computeCubicEq(x[i], q.ma[c]);
			c++;
			//q.ma[i][q.c - 1] = 0;
		}
		else {
			//if ((x[i][0] != 0 || x[i][1] != 0 || x[i][2] != 0) &&
				//(x[i][3] != 0 || x[i][4] != 0 || x[i][5] != 0)) {
			computeCubicEq(x[i], q.ma[c]);
			q.ma[c][q.c - 1] ^= 1;
			c++;
			//}
		}
	}
	cout << "c:" << c << endl;
	outputM(q);
	cout << "after gauss" << endl;
	gauss(q, q.c - 1);
	outputM(q);
	cout << "simplify:" << endl;
	simplify(q, q.c - 1);
	outputM(q);

	for (int i = 0; i < t; i++) {
		bool c0 = (x[i][0] & x[i][3]) ^ (x[i][1] & x[i][4]) ^ (x[i][2] & x[i][5]);
		c0 = c0 ^ ((x[i][0] ^ 1) & (x[i][1] ^ 1) & (x[i][2] ^ 1));
		c0 = c0 ^ 1;

		bool c1 = ((x[i][0] ^ 1) & (x[i][1] ^ 1) & (x[i][2] ^ 1));
		c1 = c1 ^ ((x[i][3] ^ 1) & (x[i][4] ^ 1) & (x[i][5] ^ 1));

		if (valid[i]) {
			if (c0 != 0 && c1 != 0)
				cout << "wrong valid" << endl;
		}
		else {
			if (c0 == 0 && c1 == 0) {
				cout << x[i][0] << x[i][1] << x[i][2] << " -> " << x[i][3] << x[i][4] << x[i][5] << endl;
				cout << "wrong invalid" << endl;
			}
		}
	}
}

void LowMC::computeQuadraticEq(bool x[],bool row[]) {
	int cnt = 0;
	for (int i = 0; i < 6; i++) {
		for (int j = i+1; j < 6; j++) {
			row[cnt] = (x[i] & x[j]);
			cnt++;
		}
	}
	for (int i = 0; i < 6; i++) {
		row[cnt] = x[i];
		cnt++;
	}
}

void LowMC::computeCubicEq(bool x[],bool row[]) {
	int cnt = 0;
	for (int i = 0; i < 6; i++) {
		for (int j = i+1; j < 6; j++) {
			for (int z = j + 1; z < 6; z++) {
				row[cnt] = (x[i] & x[j] & x[z]);
				cnt++;
			}
		}
	}
	for (int i = 0; i < 6; i++) {
		for (int j = i + 1; j < 6; j++) {
			row[cnt] = (x[i] & x[j]);
			cnt++;
		}
	}
	for (int i = 0; i < 6; i++) {
		row[cnt] = x[i];
		cnt++;
	}
}



/*****************************
*
*matrix operations
*
*****************************/

void LowMC::matrixMul(M& m, bool x[], bool y[]) {
	for (int i = 0; i < m.r; i++) {
		y[i] = 0;
		for (int j = 0; j < m.c; j++) {
			y[i] = y[i] ^ (m.ma[i][j] & x[j]);
		}
	}
}

void LowMC::matrixMul(M& m, vector<bool>& x, vector<bool>& y){
	for (int i = 0; i < m.r; i++) {
		y[i] = 0;
		for (int j = 0; j < m.c; j++) {
			y[i] = y[i] ^ (m.ma[i][j] & x[j]);
		}
	}
}

void LowMC::matrixMul(M& m, bool x[]) {
	bool y[256];
	for (int i = 0; i < m.r; i++) {
		y[i] = 0;
		for (int j = 0; j < m.c; j++) {
			y[i] = y[i] ^ (m.ma[i][j] & x[j]);
		}
	}
	for (int i = 0; i < m.r; i++) {
		x[i] = y[i];
	}
}

void LowMC::matrixMul(M& m1, M& m2, M& m3) {
	//cout << m1.r << " " << m1.c <<" "<<m2.c<< endl;
	for (int i = 0; i < m1.r; i++) {
		for (int j = 0; j < m2.c; j++) {
			m3.ma[i][j] = 0;
			for (int k = 0; k < m1.c; k++) {
				m3.ma[i][j] = m3.ma[i][j] ^ (m1.ma[i][k] & m2.ma[k][j]);
			}
		}
	}
	//outputMatrix(m3);
	for (int i = 0; i < m2.r; i++) {
		for (int j = 0; j < m2.c; j++) {
			m2.ma[i][j] = m3.ma[i][j];
		}
	}
}

void LowMC::matrixMul(M& m1, M& m2) {
	M m3;
	m3.r = m1.r;
	m3.c = m2.c;
	//cout << m1.r << " " << m1.c <<" "<<m2.c<< endl;
	for (int i = 0; i < m1.r; i++) {
		for (int j = 0; j < m2.c; j++) {
			m3.ma[i][j] = 0;
			for (int k = 0; k < m1.c; k++) {
				m3.ma[i][j] = m3.ma[i][j] ^ (m1.ma[i][k] & m2.ma[k][j]);
			}
		}
	}
	//outputMatrix(m3);
	for (int i = 0; i < m2.r; i++) {
		for (int j = 0; j < m2.c; j++) {
			m2.ma[i][j] = m3.ma[i][j];
		}
	}
}

void LowMC::clearMatrix(M& m) {
	for (int i = 0; i < m.r; i++) {
		for (int j = 0; j < m.c; j++) {
			m.ma[i][j] = 0;
		}
	}
}

void LowMC::matrixEq(M& src, M& dec) {
	dec.r = src.r;
	dec.c = src.c;
	for (int i = 0; i < src.r; i++) {
		for (int j = 0; j < src.c; j++) {
			dec.ma[i][j] = src.ma[i][j];
		}
	}
}

void LowMC::gauss(M& eqSys, int col) {
	int variableNum = col;
	bool isFirst = false;
	int targetRow = 0;

	for (int i = 0; i < variableNum; i++) {
		isFirst = true;
		for (int j = targetRow; j < eqSys.r; j++) {
			if (isFirst && eqSys.ma[j][i]) {
				isFirst = false;
				swap(eqSys.ma[j], eqSys.ma[targetRow]);
				targetRow++;
			}
			else {
				if (eqSys.ma[j][i]) {//apply Gauss
					for (int k = i; k < eqSys.c; k++) {
						eqSys.ma[j][k] ^= eqSys.ma[targetRow - 1][k];
					}
				}
			}
		}
	}
}

void LowMC::simplify(M& m, int col) {
	//further simplify
	int varNum = col;
	int index = 0;
	bool find = false;
	for (int i = 0; i < m.r; i++) {
		find = false;
		for (int j = index; j < varNum; j++) {
			if (m.ma[i][j]) {
				index = j;
				find = true;
				break;
			}
		}
		if (find) {//it is 1 in connectH[i][index], eliminate 1 above
			//cout << "find " << index << endl;
			for (int k = 0; k < i; k++) {
				if (m.ma[k][index]) {//add row[i] to row [k]
					for (int t = i; t < m.c; t++) {
						m.ma[k][t] = m.ma[k][t] ^ m.ma[i][t];
					}
				}
			}
			index++;
		}
	}
}

void LowMC::storeSolutions(vector<vector<bool> >& sol, M& eqSys, int& solNum) {
	vector<int> lead;
	vector<int> freebits;
	freebits.clear();
	lead.clear();
	bool* isFree;
	isFree = new bool[eqSys.c - 1];
	memset(isFree, 1, eqSys.c - 1);

	int start = 0;
	for (int r = 0; r < eqSys.r; r++) {
		while (start < eqSys.c - 1 && eqSys.ma[r][start] == 0) {
			start++;
		}
		if (start == eqSys.c - 1) {
			break;
		}
		lead.push_back(start);
		isFree[start] = false;
		start++;
	}

	if (lead.size() < eqSys.r) {
		for (int j = lead.size(); j < eqSys.r; j++) {
			if (eqSys.ma[j][eqSys.c - 1] != 0) {
				solNum = 0;
				return;
			}
		}
	}

	for (int i = 0; i < eqSys.c - 1; i++) {
		if (isFree[i]) {
			freebits.push_back(i);
		}
	}
	//cout << "free size:" << freebits.size() << endl;
	//cout << "lead size:" << lead.size() << endl;*/

	vector<bool> eachsol;
	eachsol.clear();
	eachsol.resize(eqSys.c - 1);
	int solSize = 1 << freebits.size();
	for (int i = 0; i < solSize; i++) {
		for (int j = 0; j < freebits.size(); j++) {
			eachsol[freebits[j]] = (i >> j) & 0x1;
		}
		for (int k = lead.size() - 1; k >= 0; k--) {
			//compute eachsol[lead[k]] use row= k
			eachsol[lead[k]] = eqSys.ma[k][eqSys.c - 1];
			for (int j = lead[k] + 1; j < eqSys.c - 1; j++) {
				if (eqSys.ma[k][j] == 1) {
					eachsol[lead[k]] = eachsol[lead[k]] ^ eachsol[j];
				}
			}
		}
		solNum++;
		sol.push_back(eachsol);
	}

	delete[]isFree;
	freebits.clear();
	lead.clear();
	eachsol.clear();
}

/*****************************
*
*output functions
*
*****************************/


void LowMC::outputM(M mat) {
	for (int i = 0; i < mat.r; i++) {
		for (int j = 0; j < mat.c; j++) {
			cout << mat.ma[i][j] ;
			//if (j == N - 1) {
				//cout << "  ";
			//}
		}
		cout << endl;
	}
}

void LowMC::outputArray(bool vec[], int size) {
	for (int i = 0; i < size; i++) {
		cout << vec[i];
	}
	cout << endl;
}
