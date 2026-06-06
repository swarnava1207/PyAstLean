import numpy as np
import math


def sigmoid(x):
    return 1.0 / (1.0 + math.exp(-x))


def predict(x, w1, b1, w2, b2):
    # Forward pass through a 2 -> 2 -> 1 network.
    h0 = sigmoid(np.dot(x, w1[0]) + b1[0])
    h1 = sigmoid(np.dot(x, w1[1]) + b1[1])
    hidden = [h0, h1]
    return sigmoid(np.dot(hidden, w2[0]) + b2[0])


def mean_squared_error(xs, ys, w1, b1, w2, b2):
    total = 0.0
    for i in range(len(xs)):
        diff = predict(xs[i], w1, b1, w2, b2) - ys[i]
        total = total + diff * diff
    return total / len(xs)


def main():
    # XOR is not linearly separable, so a single layer cannot solve it -- the
    # hidden layer is what makes this learnable.
    xs = [[0.0, 0.0], [0.0, 1.0], [1.0, 0.0], [1.0, 1.0]]
    ys = [0.0, 1.0, 1.0, 0.0]

    # Fixed initial weights so the run is reproducible (no RNG needed).
    w1 = [[0.5, -0.4], [0.9, 1.0]]
    b1 = [0.1, -0.2]
    w2 = [[0.7, -0.8]]
    b2 = [0.3]

    lr = 0.5
    epochs = 4000

    print("=== Training a neural net on XOR (NumPy + math) ===")
    print(f"initial loss: {mean_squared_error(xs, ys, w1, b1, w2, b2)}")

    for epoch in range(epochs):
        for i in range(len(xs)):
            x = xs[i]
            y = ys[i]

            # Forward pass, keeping the hidden activations for backprop.
            h0 = sigmoid(np.dot(x, w1[0]) + b1[0])
            h1 = sigmoid(np.dot(x, w1[1]) + b1[1])
            hidden = [h0, h1]
            out = sigmoid(np.dot(hidden, w2[0]) + b2[0])

            # Backward pass: gradients of 1/2 the squared error.
            d_out = (out - y) * out * (1.0 - out)
            d_h0 = d_out * w2[0][0] * h0 * (1.0 - h0)
            d_h1 = d_out * w2[0][1] * h1 * (1.0 - h1)

            # Gradient-descent step (rebuild each weight row in place).
            w2[0] = [w2[0][0] - lr * d_out * h0, w2[0][1] - lr * d_out * h1]
            b2 = [b2[0] - lr * d_out]
            w1[0] = [w1[0][0] - lr * d_h0 * x[0], w1[0][1] - lr * d_h0 * x[1]]
            w1[1] = [w1[1][0] - lr * d_h1 * x[0], w1[1][1] - lr * d_h1 * x[1]]
            b1 = [b1[0] - lr * d_h0, b1[1] - lr * d_h1]

        if (epoch + 1) % 1000 == 0:
            print(f"epoch {epoch + 1}: loss = {mean_squared_error(xs, ys, w1, b1, w2, b2)}")

    print("learned predictions:")
    for i in range(len(xs)):
        p = predict(xs[i], w1, b1, w2, b2)
        label = 1 if p > 0.5 else 0
        print(f"  {xs[i]} -> {p}  (class {label}, target {int(ys[i])})")

if __name__ == "__main__":
    main()
