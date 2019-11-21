#include <random>
#include <iostream>
#include <chrono>
#include <numeric>
#include <unordered_set>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <array>

using namespace std::chrono;

class PermGen
{
public:
	PermGen()
	{
		unsigned char tmp[std::mt19937::state_size];
		std::random_device rand;
		std::generate(std::begin(tmp), std::end(tmp), std::ref(rand));
		std::seed_seq seq(std::begin(tmp), std::end(tmp));
		rng = std::mt19937(seq);
	}

	int operator()(int start, int end)
	{
		std::uniform_int_distribution<> dist(start, end);
		return dist(rng);
	}

	std::mt19937 rng;
};

struct Mat
{
	std::vector<float> data;
	int w = 0;
	int h = 0;
};

struct Move
{
	int a, b, cost;
};

// Compares two intervals according to staring times. 
bool compareMoves(Move m1, Move m2)
{
	return (m1.cost < m2.cost);
}


class QAP
{
public:
	QAP(const std::string& file_name)
	{
		std::ifstream file(file_name);

		int n;
		file >> n;

		std::vector<float> tmp_vec;
		tmp_vec.reserve(n * n);

		for (int i = 0; i < n * n; ++i)
		{
			int tmp;
			file >> tmp;
			tmp_vec.push_back(tmp);
		}

		a = { tmp_vec, n, n };

		tmp_vec.clear();

		for (int i = 0; i < n * n; ++i)
		{
			int tmp;
			file >> tmp;
			tmp_vec.push_back(tmp);
		}

		b = { tmp_vec, n, n };

		current_permutation = std::vector<int>(n, 0);
		partial_costs = std::vector<float>(n * n, 0);
	}

	void init_random()
	{
		const int size = static_cast<int>(current_permutation.size());

		for (int i = 0; i < size; ++i)
			current_permutation[i] = i;

		for (int i = size - 1; i >= 0; --i)
			std::swap(current_permutation[i], current_permutation[rng(0, i)]);
	}

	void gen_swap(const std::vector<int>& perm, std::vector<int>& out, int i, int j)
	{
		std::memcpy(out.data(), perm.data(), sizeof(int) * perm.size());
		std::swap(out[i], out[j]);
	}

	float obj_func(const std::vector<float>& costs)
	{
		float sum = 0;

		for (const auto part : costs)
			sum += part;

		return sum;
	}

	void recalculate_obj(const std::vector<int>& perm, std::vector<float>& costs, int i, int j)
	{
		const int size = perm.size();

		//recalculate i, j rows
		for (int k = 0; k < size; ++k)
			costs[i * size + k] = a.data[i * a.w + k] * b.data[perm[i] * b.w + perm[k]];

		for (int k = 0; k < size; ++k)
			costs[j * size + k] = a.data[j * a.w + k] * b.data[perm[j] * b.w + perm[k]];

		//recalculate i, j columns
		for (int k = 0; k < size; ++k)
			costs[k * size + i] = a.data[k * a.w + i] * b.data[perm[k] * b.w + perm[i]];

		for (int k = 0; k < size; ++k)
			costs[k * size + j] = a.data[k * a.w + j] * b.data[perm[k] * b.w + perm[j]];
	}

	float init_obj_func(const std::vector<int>& perm)
	{
		const int size = static_cast<int>(current_permutation.size());

		for (int i = 0; i < size; ++i) {
			for (int j = 0; j < size; ++j) {
				partial_costs[i * size + j] = a.data[i * a.w + j] * b.data[perm[i] * b.w + perm[j]];
			}
		}

		return obj_func(partial_costs);
	}

	Move get_move(std::vector<Move>& moves_list, std::vector<float>& taboo_matrix, const int size, const int current_obj, const int best_obj) {
		Move min_taboo = moves_list[0];
		for (auto move : moves_list) {
			if (taboo_matrix[move.a * size + move.b] > 0) {
				// if move is on taboo list but is good - return it
				if (current_obj + move.cost < best_obj) return move;
				if (taboo_matrix[move.a * size + move.b] < taboo_matrix[min_taboo.a * size + min_taboo.b]) min_taboo = move;
			}
			else return move;
		}
		// if every move is on taboo list - return the least taboo move
		return min_taboo;
	}

	std::tuple<std::vector<int>, std::vector<int>, std::vector<float>> taboo(const std::vector<int>& perm, int taboo_ttl, int no_impr_stop)
	{
		const int size = static_cast<int>(perm.size());
		int no_improvement = 0;

		std::vector<int> init_perm(perm);
		std::vector<int> neighbour(perm);
		std::vector<int> best(perm);
		float best_obj_func = init_obj_func(perm);
		float current_obj_func = init_obj_func(perm);
		std::vector<float> neighbour_partials(partial_costs);

		auto taboo_matrix = std::vector<float>(size * size, 0);
		std::vector<Move> moves_list; moves_list.reserve(100000);
		std::vector<float> scores; scores.reserve(100000);

		while (no_improvement < no_impr_stop) {

			// build moves list
			for (int i = 0; i < size - 1; ++i) {
				for (int j = i + 1; j < size; ++j) {
					// generate neighbour
					gen_swap(current_permutation, neighbour, i, j);

					// get neighbour obj func
					std::memcpy(neighbour_partials.data(), partial_costs.data(), sizeof(float) * partial_costs.size());
					recalculate_obj(neighbour, neighbour_partials, i, j);
					const float neighbour_obj_func = obj_func(neighbour_partials);

					// add move to moves list
					const Move move = { i, j, (neighbour_obj_func - current_obj_func) };
					moves_list.push_back(move);
				}
			}

			// sort moves list
			std::sort(moves_list.begin(), moves_list.end(), compareMoves);

			const Move best_move = get_move(moves_list, taboo_matrix, size, current_obj_func, best_obj_func);

			// actualize taboo matrix - subtract 1 from every non-zero cell
			for (int i = 0; i < size - 1; ++i) {
				for (int j = i + 1; j < size; ++j) {
					if (taboo_matrix[i * size + j] != 0) {
						taboo_matrix[i * size + j] -= 1;
					}
				}
			}

			// actualize taboo matrix with new move
			taboo_matrix[best_move.a * size + best_move.b] = taboo_ttl;

			// set current solution as previous with new move
			gen_swap(current_permutation, neighbour, best_move.a, best_move.b);
			std::memcpy(current_permutation.data(), neighbour.data(), sizeof(int) * neighbour.size());

			// recalculate costs and save it in current partial costs
			recalculate_obj(neighbour, neighbour_partials, best_move.a, best_move.b);
			std::memcpy(partial_costs.data(), neighbour_partials.data(), sizeof(float) * neighbour_partials.size());

			// set current obj function
			current_obj_func += best_move.cost;

			// save as best if best
			if (current_obj_func < best_obj_func) {
				best_obj_func = current_obj_func;
				std::memcpy(best.data(), current_permutation.data(), sizeof(int) * current_permutation.size());
				// reset no improvement counter
				no_improvement = 0;
			}
			else
				no_improvement++;

			scores.push_back(best_obj_func);
			moves_list.clear();

		}

		return std::make_tuple(init_perm, best, scores);
	}


	std::vector<int> getCurrentPerm() {
		return current_permutation;
	}

	int GetSwaps()
	{
		const int tmp = swaps;
		swaps = 0;
		return tmp;
	}

private:
	Mat a, b;
	PermGen rng;

	std::vector<int> current_permutation;
	std::vector<float> partial_costs;
	int swaps = 0;
};

std::tuple<std::vector<std::vector<int>>, std::vector<std::vector<int>>, std::vector<std::vector<float>>, std::vector<int>> time_count(QAP& instance, int algorithm, int how_many_times, int ts_ttl, int no_impr_stop)
{
	int licznik = 0;
	auto time0 = high_resolution_clock::now();
	high_resolution_clock::time_point start;

	std::vector<std::vector<int>> init_perms;
	std::vector<std::vector<int>> best_perms;
	std::vector<std::vector<float>> runs;
	std::vector<int> time_counts;
	std::tuple<std::vector<int>, std::vector<int>, std::vector<float>> result;

	time_counts.reserve(10000);
	init_perms.reserve(how_many_times);
	best_perms.reserve(how_many_times);
	runs.reserve(how_many_times);

	// alokacja pami�ci dla result?

	do {
		instance.init_random();
		start = high_resolution_clock::now();

		switch (algorithm) {

		case 5:
			result = instance.taboo(instance.getCurrentPerm(), ts_ttl, no_impr_stop);
		}

		licznik++;
		init_perms.push_back(std::move(std::get<0>(result)));
		best_perms.push_back(std::move(std::get<1>(result)));
		runs.push_back(std::move(std::get<2>(result)));
		time_counts.push_back((high_resolution_clock::now() - start).count());

	} while (licznik < how_many_times || std::chrono::duration_cast<std::chrono::milliseconds>(high_resolution_clock::now() - time0).count() < 100);

	return std::make_tuple(init_perms, best_perms, runs, time_counts);
}




int main(int argc, char** argv)
{
	std::string path = argv[1];
	int algorithm = std::stoi(argv[2]);
	int how_many_times = std::stoi(argv[3]);
	int ts_ttl = std::stoi(argv[4]);
	int no_impr_stop = std::stoi(argv[5]);

	QAP instance(path);
	auto tup = time_count(instance, algorithm, how_many_times, ts_ttl, no_impr_stop);
	//auto&& [init_perm, times, scores, swaps, best_perm] = time_count(instance, algorithm, time_random);
	std::vector<std::vector<int>> init_perms = std::get<0>(tup);
	std::vector<std::vector<int>> best_perms = std::get<1>(tup);
	std::vector<std::vector<float>> scores = std::get<2>(tup);
	std::vector<int> times = std::get<3>(tup);

	std::cout << "number of runs: ";
	std::cout << scores.size() << "\n";

	for (const auto& s : scores) {
		for (const auto& f : s) {
			std::cout << f << " ";
		}
		std::cout << "\n";
	}

	std::cout << "\n";
	std::cout << "times:\n";

	for (int i = 0; i < times.size(); i++) {
		std::cout << std::fixed << times[i] << "\n";
	}

	std::cout << "\n";
	std::cout << "initial permutations:\n";

	for (const auto& s : init_perms) {
		for (const auto& f : s) {
			std::cout << f << " ";
		}
		std::cout << "\n";
	}

	std::cout << "\n";
	std::cout << "best permutations:\n";

	for (const auto& s : best_perms) {
		for (const auto& f : s) {
			std::cout << f << " ";
		}
		std::cout << "\n";
	}

	std::cout << "\n";

	return 0;
}