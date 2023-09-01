#include "LowMC.h"
#include <iostream>
#include <fstream>
#include <string>
#include <iomanip>
#include <ctime>
#include <random>
using namespace std;

static double C(int n, int m)
{
	if (m < n - m) m = n - m;
	double ans = 1;
	for (int i = m + 1; i <= n; i++) ans *= i;
	for (int i = 1; i <= n - m; i++) ans /= i;
	return ans;
}
void computeComplexity(int r1, int r2, int t, int e, int n,int k, int r,int m,int u1,int h,int lambda,int uu1) {
	double t0 = 1.86 * m * (r1 + r2) - n;
	int a = (67 * h + 80) / 81;
	double klog1 = pow(2 * a, 2) * (k + 3 * (h - a));
	double klog2 = (double)pow(14 * lambda, 2) * (C(k + 3 * h - 5 * a, 2) + k + 3 * h - 5 * a + 1);
	int eps = 14 * lambda - uu1 * (uu1 - 1) / 2 - uu1;
	double klog3 = (double)pow(2, k + 3 * h - 5 * a - uu1) * (uu1 + eps) * (pow(uu1, 2) + uu1 * eps + k + 3 * h - 5 * a);
	double klog = log2((klog1+klog2+klog3) / double(r * n * n * 2));
	t0 = t0 + klog;

	double t1 = 1.86*t;

	double t2 = 1.86 * (m * r2+e);
	double b = 0;
	for (int i = 0; i <= 2 * u1 + 4; i++)
	{
		b += C(3 * m * (r1 - 1) - 3 * t  - u1, i);
	}
	double t3 = 1.86 * (m * r2 + e) + 1.86 * t - (n - 3 * m * r1 + 3 * e + 3 * t) + log2((24 * log2(3 * m * (r1 - 1) - 3 * t) * pow(2, u1) * b + 4 * (u1 + 1) * (3 * m * (r1 - 1) - 3 * t - u1) * pow(2, 3 * m * (r1 - 1) - 3 * t - u1)) / double(r * n * n * 2));
	
	double t4 = pow(2, t3) + pow(2, t1);
	t4 = log2(t4);
	double t5 = pow(2, t2) + pow(2, t1);
	t5 = log2(t5);
	if (3 * m * (r1 - 1) - 3 * t>0)
	{
		cout << t0 << " "  << t4 << endl;
	}
	else {
		cout << t0 << " " << t5 << endl;
	}
	
}

void testSuccessRate() {
	LowMC lowmc;
	bool y[6];
	
	bool p0[N], k[N], c0[N], p1[N], c1[N];
	vector<vector<bool> > SOut0, SOut1, LOut0, LOut1;
	SOut0.resize(R), SOut1.resize(R), LOut0.resize(R), LOut1.resize(R);
	for (int i = 0; i < R; i++) {
		SOut0[i].resize(N), SOut1[i].resize(N), LOut0[i].resize(N), LOut1[i].resize(N);
	}
	vector<vector<bool> > SOutDiff, LOutDiff;
	SOutDiff.resize(R - 2), LOutDiff.resize(R - 2);
	for (int i = 0; i < R - 2; i++) {
		SOutDiff[i].resize(N), LOutDiff[i].resize(N);
	}

	srand(time(NULL));
	int success = 0;
	int CNT = 8000;

	std::mt19937 mt;         
	std::random_device rnd; 
	mt.seed(rnd());
	
	for (int i = 0; i < CNT; i++) {
		for (int i = 0; i < N / 16; i++) {
			unsigned int v0 = 0, v1 = 0;
			v0 = mt(), v1 = mt();
			//v0 = 0xffff, v1 = 0xffff;
			//v0 = 0xffff, v1 = 0;
			for (int j = 0; j < 16; j++) {
				p0[i * 16 + j] = (v0 >> j) & 0x1;
				k[i * 16 + j] = (v1 >> j) & 0x1;
			}
		}

		lowmc.encryptionDetails(p0, k, c0, R - 2, LOut0, SOut0);

		bool diff[N] = {
			0,0,0,0,1,0,1,1,1,1,1,0,0,1,0,0,0,0,1,1,0,1,0,0,1,0,1,0,0,1,0,0,0,1,0,0,0,1,1,0,0,1,1,1,1,1,0,0,0,0,1,1,0,0,0,1,0,1,0,1,1,1,0,0,0,0,1,1,1,0,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,1,1,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,0,0,0,1,1,1,0,1,1,1,0,1,0,
		};
		for (int i = 0; i < N; i++) {
			p1[i] = p0[i] ^ diff[i];
		}
		lowmc.encryptionDetails(p1, k, c1, R - 2, LOut1, SOut1);

		/*for (int j = 0; j < N; j++) {
			cout << (LOut0[41][j] ^ LOut1[41][j]) << ",";
		}
		cout << endl;
		system("pause");*/

		int rounds = R - 2;
		int inactiveCnt = 0;
		//check the last 98 S-boxes
		for (int i = rounds; i > rounds - 98; i--) {
			if (SOut0[i - 1][0] == SOut1[i - 1][0]
				&& SOut0[i - 1][1] == SOut1[i - 1][1]
				&& SOut0[i - 1][2] == SOut1[i - 1][2]) {
				inactiveCnt++;
			}
		}
		if (98 - inactiveCnt >= 82) {
			success++;
			
			for (int i = 0; i < R - 2; i++) {
				for (int j = 0; j < N; j++) {
					SOutDiff[i][j] = SOut0[i][j] ^ SOut1[i][j];
					LOutDiff[i][j] = LOut0[i][j] ^ LOut1[i][j];
				}
			}
			
			


		}

		/*if (i % 100 == 0) {
			cout << i << ":" << success << endl;
		}*/
	}

	cout <<"rate:"<< (double)(success) / CNT << endl;

	/*///
	//retrieve the internal difference for verification of the difference enumeration
	int l = 47;
	vector<bool> u(3 * l);
	for (int i = 42; i < 42 + l; i++) {
		u[(i - 42) * 3] = SOut0[i][0] ^ SOut1[i][0];
		u[(i - 42) * 3 + 1] = SOut0[i][1] ^ SOut1[i][1];
		u[(i - 42) * 3 + 2] = SOut0[i][2] ^ SOut1[i][2];
	}

	vector<bool> gamma(N);
	for (int i = 0; i < N; i++) {
		//gamma[i - 3] = LOut0[42 + l - 1][i] ^ LOut1[42 + l - 1][i];
		gamma[i] = LOut0[42+l-1][i] ^ LOut1[42+l-1][i];
	}

	vector<bool> finalOut(N);
	for (int i = 0; i < N; i++) {
		finalOut[i]= LOut0[102][i] ^ LOut1[102][i];
	}

	cout << "value for u:" << endl;
	for (int i = 0; i < u.size(); i++) {
		cout << u[i] << ",";
	}
	cout << endl;
	cout << "value for gamma:" << endl;
	for (int i = 0; i < gamma.size(); i++) {
		cout << gamma[i] << ",";
	}
	cout << endl;

	cout << "value for final output diff:" << endl;
	for (int i = 0; i < finalOut.size(); i++) {
		cout << finalOut[i] << ",";
	}
	cout << endl;

	u.clear();
	gamma.clear();
	*////

	for (int i = 0; i < R; i++) {
		SOut0[i].clear(), SOut1[i].clear(), LOut0[i].clear(), LOut1[i].clear();
	}
	SOut0.clear(), SOut1.clear(), LOut0.clear(), LOut1.clear();
}

void testcrossbred() {
	LowMC lowmc;
	bool y[6] = {0,1,0,1,0,1,};

	bool p0[N] = {
		1,1,1,0,0,0,0,0,0,0,0,0,1,0,0,1,1,1,0,1,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,1,0,0,1,1,1,0,0,0,1,0,0,0,1,1,0,1,1,1,1,0,0,1,1,0,0,1,0,0,0,0,1,1,1,0,1,1,0,1,1,1,0,0,0,0,1,0,1,0,0,1,0,1,1,1,0,0,1,1,0,0,0,1,1,0,0,0,1,0,0,0,0,0,1,0,1,1,1,1,0,1,1,0,1,0,0,0,0,0,0,1,1,0, };


	bool k[N] = {
		1,1,1,0,1,1,0,1,1,0,0,1,0,1,1,0,1,1,0,1,0,0,1,0,1,0,0,1,1,1,1,0,0,0,1,0,1,1,0,1,0,0,0,0,0,1,0,1,0,0,1,0,1,0,0,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,1,1,0,1,1,0,1,0,0,1,0,0,0,1,1,1,1,1,1,1,1,0,1,0,0,1,1,0,0,0,1,0,0,1,1,0,0,1,1,1,0,0,1,0,0,0,0,0,1,0,0,1,1,0,
	};

	bool c0[N], p1[N], c1[N];
	vector<vector<bool> > SOut0, SOut1, LOut0, LOut1;
	SOut0.resize(R), SOut1.resize(R), LOut0.resize(R), LOut1.resize(R);
	for (int i = 0; i < R; i++) {
		SOut0[i].resize(N), SOut1[i].resize(N), LOut0[i].resize(N), LOut1[i].resize(N);
	}
	vector<vector<bool> > SOutDiff, LOutDiff;
	SOutDiff.resize(R - 2), LOutDiff.resize(R - 2);
	for (int i = 0; i < R - 2; i++) {
		SOutDiff[i].resize(N), LOutDiff[i].resize(N);
	}

	srand(time(NULL));
	int success = 0;



	cout << endl;
	lowmc.encryptionDetails(p0, k, c0, R - 2, LOut0, SOut0);

	bool diff[N] = {
		0,0,0,0,1,0,1,1,1,1,1,0,0,1,0,0,0,0,1,1,0,1,0,0,1,0,1,0,0,1,0,0,0,1,0,0,0,1,1,0,0,1,1,1,1,1,0,0,0,0,1,1,0,0,0,1,0,1,0,1,1,1,0,0,0,0,1,1,1,0,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,0,1,1,0,0,1,1,1,1,1,1,1,1,1,0,0,1,1,0,1,1,1,0,1,1,1,1,0,0,0,0,1,1,1,0,1,1,1,0,1,0,
	};
	for (int i = 0; i < N; i++) {
		p1[i] = p0[i] ^ diff[i];
	}
	lowmc.encryptionDetails(p1, k, c1, R - 2, LOut1, SOut1);

	/*for (int j = 0; j < N; j++) {
		cout << (LOut0[41][j] ^ LOut1[41][j]) << ",";
	}
	cout << endl;
	system("pause");*/

	int rounds = R - 2;

	for (int i = 0; i < R - 2; i++) {
		for (int j = 0; j < N; j++) {
			SOutDiff[i][j] = SOut0[i][j] ^ SOut1[i][j];
			LOutDiff[i][j] = LOut0[i][j] ^ LOut1[i][j];
		}
	}
	int inactiveCnt = 0;
	//check the last 98 S-boxes
	for (int i = rounds; i > rounds - 98; i--) {
		if (SOut0[i - 1][0] == SOut1[i - 1][0]
			&& SOut0[i - 1][1] == SOut1[i - 1][1]
			&& SOut0[i - 1][2] == SOut1[i - 1][2]) {
			inactiveCnt++;
		}
	}

	for (int i = 0; i < pow(2, 6); i++) {
	

		if (98 - inactiveCnt >= 82) {
			success++;

			for (int i = 0; i < R - 2; i++) {
				for (int j = 0; j < N; j++) {
					SOutDiff[i][j] = SOut0[i][j] ^ SOut1[i][j];
					LOutDiff[i][j] = LOut0[i][j] ^ LOut1[i][j];
				}
			}
			
			for (int j = 0; j < 6; j++) {

				y[j] = (i >> j) & 0x1;
				}
				


				lowmc.keyRecovery(k, c0, R - 2, LOut0, SOut0, SOutDiff, LOutDiff, y);


			



			/*if (i % 100 == 0) {
				cout << i << ":" << success << endl;
			}*/
		}
	
		
		
	}
	for (int i = 0; i < R; i++) {
		SOut0[i].clear(), SOut1[i].clear(), LOut0[i].clear(), LOut1[i].clear();
	}
	SOut0.clear(), SOut1.clear(), LOut0.clear(), LOut1.clear();
}

	
void findInputDiff() {
		
	LowMC lowmc;
	bool x[N];
	for (int i = 0; i < N; i++) {
		x[i] = 1;
	}
	lowmc.findInputDifference(x);
}

void computeDh() {
	//the input difference
	bool x[N] = {
		1,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,1,1,1,0,1,1,1,1,0,1,0,0,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,1,1,1,0,0,1,1,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,0,1,0,1,1,0,1,1,0,1,1,
	};
	LowMC lowmc;
	lowmc.enumerateDiffForwards(x);
}
void computeg()
{
	LowMC lowmc;
	bool x0[N] = {
		1,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,1,1,1,0,1,1,1,1,0,1,0,0,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,1,1,1,0,0,1,1,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,0,1,0,1,1,0,1,1,0,1,1,
	};

	//online
	bool ga[125] = {
			1,0,0,0,1,1,0,1,1,1,1,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,1,1,1,1,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,1,0,
	};
	
}
void offline() {
	LowMC lowmc;
	bool x0[N] = {
		1,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,1,1,1,0,1,1,1,1,0,1,0,0,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,1,1,1,0,0,1,1,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,0,1,0,1,1,0,1,1,0,1,1,
	};
	lowmc.constructPQ(x0);
}



void online() {
	LowMC lowmc;
	bool x0[N] = {
		1,0,1,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,1,1,1,0,1,1,1,1,0,1,0,0,1,1,1,1,1,1,0,1,0,1,1,1,1,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,1,1,1,0,0,1,1,1,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,0,1,0,1,1,0,1,1,0,1,1,
	};
	bool ga[125] = {
			1,0,0,0,1,1,0,1,1,1,1,0,0,1,0,0,1,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,1,0,1,1,1,1,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,1,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,1,1,0,1,0,
	};
	//find (u1,...,uq) that satisfies the condition of ga.
	lowmc.constructdinur(ga, x0);
	//the cubic equations used in Dinur's algorithm.
	lowmc.constructForwardDiffR1(ga);
}

int main() {
	int cmd = 0;
	while (1) {
		cout << endl;
		cout << "*******************************************************************" << endl;
		cout << "*Notice 1: If you input 1, the file uvalue.txt will be regenerated." << endl;
		cout << "*However, when you input 2/3, the file uvalue.txt is needed." << endl;
		cout << "*So, if you first input 1, wait until command-1 is finished before doing other experiments." << endl;
		cout << "*******************************************************************" << endl;
		cout << "0 -> exit" << endl;
		cout << "1 -> precomputation (contruct tables)" << endl;
		cout << "2 -> offline" << endl;
		cout << "3 -> outputting the cubic equations used in Dinur's algorithm " << endl;
		cout << "4 -> test the success rate of key recovery" << endl; 
		cout << "5 -> test Crossbred Algorithm" << endl;
		cout << "input cmd(0/1/2/3/4/5):";
		cin >> cmd;
		if (cmd == 1) {
			computeDh();
		}
		else if (cmd == 2) {
			offline();
		}
		else if (cmd == 3) {
			online();
		}
		else if (cmd == 4) {
			testSuccessRate();
		}
		else if (cmd == 5)
		{
			testcrossbred();
		}
		else
			break;
	}

	return 0;
}
