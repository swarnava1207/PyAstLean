import math

def euclidean_distance(p1, p2):
    if len(p1) != len(p2):
        raise ValueError("Points must have the same number of dimensions")

    # Using zip, list comprehension, and math.pow
    sq_diffs = [math.pow(a - b, 2) for a, b in zip(p1, p2)]
    return math.sqrt(sum(sq_diffs))

def find_nearest_neighbor(target, dataset):
    try:
        # Calculate distances using list comprehension
        distances = [euclidean_distance(target, point) for point in dataset]

        # Find the minimum distance
        min_dist = min(distances)

        # Find the index of the minimum distance
        # Using a loop since index() might not be supported based on tests
        min_index = -1
        for i, d in enumerate(distances):
            if d == min_dist:
                min_index = i
                break

        return min_dist, dataset[min_index]
    except ValueError as e:
        print(f"Error calculating distances: {e}")
        return -1.0, []

def run_example():
    dataset = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
        [2, 1, 4]
    ]
    target_point = [2, 3, 4]
    invalid_point = [1, 2] # 2D point to trigger exception

    print("Dataset:", dataset)
    print("Target Point:", target_point)

    # Valid Case
    dist, nearest = find_nearest_neighbor(target_point, dataset)
    print("Nearest Neighbor to Target:")
    print("Point:", nearest)
    print("Distance:", dist)

    # Invalid Case
    print("\nTesting Invalid Point:")
    dist_inv, nearest_inv = find_nearest_neighbor(invalid_point, dataset)
    print("Fallback Distance:", dist_inv)

if __name__ == "__main__":
    run_example()
