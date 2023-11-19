#include <iostream>
#include <ctime>
#include <algorithm>
#include <cstdio>

using namespace std;


long long STEP;
const int maxN = 17;
const int maxM = 32;

int borders[30] = { 0, 1, 2, 4, 5, 32, 32, 32, 32, 32, 16, 18, 20, 22, 25, 27, 30, maxM, maxM, maxM, maxM };
template<typename T, size_t SZ = maxM> struct Vector {
	T a[SZ];
	int n;
	Vector() : n(0) {}
	void push_back(T x)
	{
		a[n++] = x;
	}
	void clear()
	{
		n = 0;
	}
	T operator[](int x)
	{
		return a[x];
	}
};


typedef unsigned int maskType;
typedef unsigned int bigMaskType;

bigMaskType connect[maxM];
bigMaskType use[maxN];
maskType filled[maxN];
const int block = (maxM + 1) / 2;
const maskType SIZE = (maskType)1 << (maskType)block;
Vector<int, block> lists[SIZE];

int N, ans;

int zeroes[maxN];

int index[maxN][maxM];
int cycles[maxN][maxN];
int cyclesAns[maxN][maxN];
int dist[maxM][maxM];
int distAns[maxM][maxM];

maskType preAdj[maxN][maxN][maxN];
int preDist[maxN][maxN][maxN];

void setDist(int i, int j, int value) {
	dist[i][j] = dist[j][i] = value;
	bigMaskType one = 1;
	connect[i] ^= one << (bigMaskType)j;
	connect[j] ^= one << (bigMaskType)i;
}

void setCycle(int lay, int i, int value) {
	int change = value;
	if (value == -1)
		change = cycles[lay][i];
	index[lay][change] = i;
	use[lay] ^= ((bigMaskType)1 << (bigMaskType)change);
	filled[lay] ^= (maskType)1 << ((maskType)i);
	cycles[lay][i] = value;
}

int getDist(int j, int i, int n)
{
	int d1 = abs(j - i);
	int d2 = n - d1;
	return min(d1, d2);
}


void getVector(Vector<int>& res, bigMaskType mask) {
	Vector<int, block>& v = lists[mask % SIZE];
	Vector<int, block>& u = lists[mask / SIZE];
	res.clear();
	for (int i = 0; i < v.n; i++)
	{
		res.push_back(v[i]);
	}
	for (int i = 0; i < u.n; i++)
	{
		res.push_back(u[i] + block);
	}
}
Vector<int> oldNumbers, newNumbers;

Vector<pair<int, int>, maxM* maxM > changes;

int addEdges(int* cycle, int n, maskType oldMask, maskType newMask) {
	int res = 0;
	getVector(oldNumbers, oldMask);
	getVector(newNumbers, newMask);
	for (int i = 0; i < newNumbers.n; i++) {
		int a = newNumbers[i];
		int A = cycle[a];
		for (int j = 0; j < i; j++) {
			int b = newNumbers[j];
			int B = cycle[b];
			if (dist[A][B] == -1) {
				changes.push_back(make_pair(A, B));
				setDist(A, B, preDist[n - 1][a][b]);
				res++;
			}
		}
		for (int j = 0; j < oldNumbers.n; j++) {
			int b = oldNumbers[j];
			int B = cycle[b];
			if (dist[A][B] == -1) {
				changes.push_back(make_pair(A, B));
				setDist(A, B, preDist[n - 1][a][b]);
				res++;
			}
		}
	}
	return res;
}


int addEdges(int* cycle, int i, int n) {
	int lay = n - 1;
	int res = 0;
	int a = cycle[i];
	bigMaskType mask = (use[lay] & (~connect[a])) ^ ((bigMaskType)1 << (bigMaskType)a);
	getVector(newNumbers, mask);
	for (int t = 0; t < newNumbers.n; t++) {
		int b = newNumbers[t];
		int j = index[lay][b];
		if (dist[a][b] == -1) {
			changes.push_back(make_pair(a, b));
			setDist(a, b, preDist[n - 1][i][j]);
			res++;
		}
	}
	return res;
}

Vector<int> poses[maxN];


maskType getAdj(int one, int dist, int n) {
	maskType res = 0;
	if (dist * 2 > n) {
		return 0;
	}
	else if (dist * 2 == n)
	{
		if (one - dist < 0)
			res |= (maskType)1 << (maskType)(one + dist);
		else
			res |= (maskType)1 << (maskType)(one - dist);
	}
	else if (one - dist < 0) {
		res |= (maskType)1 << (maskType)(one + dist);
		res |= (maskType)1 << (maskType)(one - dist + n);
	}
	else if (one + dist >= n) {
		res |= (maskType)1 << (maskType)(one + dist - n);
		res |= (maskType)1 << (maskType)(one - dist);
	}
	else {
		res |= (maskType)1 << (maskType)(one - dist);
		res |= (maskType)1 << (maskType)(one + dist);
	}
	return res;
}


int CNT = 0;


void printAns()
{
	for (int i = 0; i < N; i++) {
		for (int j = 0; j <= i; j++)
		{
			cout << cyclesAns[i][j] << ' ';
		}
		cout << endl;
	}
	for (int i = 0; i < ans; i++) {
		cout << i << ": ";
		for (int j = 0; j < ans; j++)
		{
			cout << distAns[i][j] << ' ';
		}
		cout << endl;
	}
	cout << endl;
	cout << endl;
}

void update(int m)
{
	if (ans > m)
	{
		CNT = 1;
		ans = m;
	}
	else
	{
		CNT++;
	}
	for (int n = 0; n < N; n++) {
		for (int j = 0; j <= n; j++) {
			cyclesAns[n][j] = cycles[n][j];
		}
	}
	for (int i = 0; i < m; i++) {
		for (int j = 0; j < m; j++) {
			distAns[i][j] = dist[i][j];
		}
	}
	printAns();
}


void checkAns()
{
	for (int n = 1; n <= N; n++)
	{
		for (int i = 0; i < n; i++)
		{
			int a = cyclesAns[n - 1][i];
			for (int j = i + 1; j < n; j++)
			{
				int b = cyclesAns[n - 1][j];
				int d = preDist[n - 1][i][j];

				if (distAns[a][b] != d)
				{
					cout << a << " " << b << " d = " << d << ", " << distAns[a][b] << endl;
				}
			}
		}
	}
}


void revertEdges(int cnt)
{
	int start = changes.n - cnt;
	for (int i = start; i < changes.n; i++) {
		setDist(changes[i].first, changes[i].second, -1);
	}
	changes.n -= cnt;
}


int t0;

void printTime()
{
	int t1 = time(0);
	int T = t1 - t0;
	printf("%02d:%02d\n", T / 60, T % 60);
}

maskType MASK;
long long tenbillions = 1e9;


void solve(int n, int num, int m) {
	int lay = n - 1;
	STEP++;
	if (STEP % tenbillions == 0)
	{
		printTime();
		cout << STEP << endl;
		cout << "n = " << n << " MASK = " << MASK << " m = " << m << endl;
		for (int i = 0; i < N - 2; i++)
		{
			cout << cycles[N - 3][i] << " ";
		}
		cout << endl;
		cout << endl;
	}
	if (num == m || zeroes[lay] == 0)
	{
		maskType all = (1 << n) - 1;
		maskType oldMask = filled[lay];
		maskType newMask = all ^ oldMask;
		getVector(poses[lay], newMask);
		for (int i = 0; i < poses[lay].n; i++) {
			setCycle(lay, poses[lay][i], m);
			m++;
		}
		int cnt = addEdges(cycles[lay], n, oldMask, newMask);
		if (n == 3)
		{
			update(m);
		}
		else
		{
			solve(n - 1, 0, m);
		}
		revertEdges(cnt);
		for (int i = 0; i < poses[lay].n; i++) {
			setCycle(lay, poses[lay][i], -1);
		}
		poses[lay].clear();
		return;
	}
	maskType all = ((maskType)1 << (maskType)n) - 1;
	maskType p = 1;
	if (zeroes[lay] != n) {
		p = all ^ filled[lay];
		int val = (p & 2) << (n - 2);
		p ^= val;
	}
	bigMaskType mask = use[lay] & connect[num];
	Vector<int, block>& v = lists[mask % SIZE];
	for (int t = 0; t < v.n; t++) {
		int i = v[t];
		p &= preAdj[n - 1][index[lay][i]][dist[num][i] - 1];
		if (p == 0)
			break;
	}
	if (p != 0)
	{
		Vector<int, block>& u = lists[mask / SIZE];
		for (int t = 0; t < u.n; t++) {
			int i = u[t] + block;
			p &= preAdj[n - 1][index[lay][i]][dist[num][i] - 1];
			if (p == 0)
				break;
		}
	}
	zeroes[lay]--;
	getVector(newNumbers, p);
	for (int t = 0; t < newNumbers.n; t++) {
		int i = newNumbers[t];
		setCycle(lay, i, num);
		int cnt = addEdges(cycles[lay], i, n);
		solve(n, num + 1, m);
		revertEdges(cnt);
		setCycle(lay, i, -1);
		if (max(num + 1 + zeroes[lay], m) >= ans)
		{
			zeroes[lay]++;
			return;
		}
	}
	zeroes[lay]++;
	if (max(num + 1 + zeroes[lay], m) < ans)
		solve(n, num + 1, m);
}




void init() {
	memset(dist, -1, sizeof dist);
	memset(cycles, -1, sizeof cycles);
	memset(index, -1, sizeof index);
	for (int n = 1; n <= N; n++)
		for (int one = 0; one < N; one++)
			for (int dist = 1; dist <= N; dist++)
			{
				preAdj[n - 1][one][dist - 1] = getAdj(one, dist, n);
			}
	for (int n = 1; n <= N; n++)
		for (int i = 0; i < n; i++)
		{
			for (int j = 0; j < n; j++)
			{
				{
					preDist[n - 1][i][j] = getDist(i, j, n);
				}
			}
		}
	for (int i = 0; i < SIZE; i++)
	{
		for (int j = 0; j < block; j++)
		{
			if (i & (1 << j))
			{
				lists[i].push_back(j);
			}
		}
	}
}


bool calc[1 << ((maxN + 1) / 2) ];
int num[maxN];

maskType revert(maskType m)
{
	int res = 0;
	while (m > 0)
	{
		res *= 2;
		res += m % 2;
		m /= 2;
	}
	return res;
}


int main()
{
	FILE* stream;
	freopen_s(&stream, "output.txt", "w", stdout);
	maskType start;
	cin >> N >> start;
	t0 = time(0);
	init();
	ans = borders[N] + 1;
	cycles[0][0] = 0;
	cycles[1][0] = 0;
	cycles[1][1] = 1;
	for (int i = 0; i < N; i++)
	{
		cycles[N - 1][i] = i;
		zeroes[i] = i + 1;
	}
	for (int i = 0; i < N; i++)
	{
		for (int j = 0; j < i; j++)
		{
			setDist(i, j, preDist[N - 1][i][j]);
		}
	}
	int L = (N + 1) / 2;
	maskType all = (1 << (N - 1)) - 1;
	for (MASK = start; MASK < (1 << L); MASK += 2)
	{
		int rev = revert(MASK);
		if (calc[rev])
		{
			continue;
		}
//		cout << MASK << endl;
		calc[MASK] = true;
		int cur = N;
		for (int i = 0; i < N - 1; i++)
		{
			if ((1 << i) & MASK) {
				cycles[N - 2][i] = i;
			}
			else
			{
				cycles[N - 2][i] = cur++;
			}
		}
		int cnt = addEdges(cycles[N - 2], N - 1, MASK, all ^ MASK);
		if (cur < ans)
			solve(N - 2, 0, cur);
		revertEdges(cnt);
	}
	printAns();
	checkAns();
	printTime();
	cout << "STEP = " << STEP << " >> " << ans << " <<" << endl;
	return 0;
}
