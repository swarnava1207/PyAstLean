import numpy as np
import math

def sigmoid(x):
    return 1.0 / (1.0 + math.exp(-x))

def relu(x):
    if x > 0.0:
        return x
    return 0.0

def dense_layer(inputs, weights, biases):
    # A fully-connected layer: one neuron per row of `weights`.
    outputs = []
    for j in range(len(weights)):
        z = np.dot(inputs, weights[j]) + biases[j]
        outputs.append(z)
    return outputs

def apply_sigmoid(xs):
    return [sigmoid(x) for x in xs]

def apply_relu(xs):
    return [relu(x) for x in xs]

def softmax(xs):
    # Numerically-stable softmax: subtract the max before exponentiating.
    m = max(xs)
    exps = [math.exp(x - m) for x in xs]
    total = sum(exps)
    return [e / total for e in exps]


def cross_entropy(probs, target):
    # Negative log-likelihood of the target class.
    return -math.log(probs[target])


def forward(features):
    # Hidden layer 1: 3 inputs -> 4 neurons, ReLU.
    w1 = [
        [0.10, -0.20, 0.30],
        [0.40, 0.50, -0.10],
        [-0.30, 0.20, 0.10],
        [0.05, -0.40, 0.25],
    ]
    b1 = [0.10, -0.20, 0.05, 0.00]

    # Hidden layer 2: 4 inputs -> 3 neurons, sigmoid.
    w2 = [
        [0.20, -0.10, 0.40, 0.10],
        [-0.30, 0.30, 0.10, -0.20],
        [0.10, 0.20, -0.40, 0.30],
    ]
    b2 = [0.00, 0.10, -0.10]

    # Output layer: 3 inputs -> 2 classes, softmax.
    w3 = [
        [0.50, -0.20, 0.30],
        [-0.40, 0.60, 0.10],
    ]
    b3 = [0.05, -0.05]

    h1 = apply_relu(dense_layer(features, w1, b1))
    h2 = apply_sigmoid(dense_layer(h1, w2, b2))
    logits = dense_layer(h2, w3, b3)
    probs = softmax(logits)
    return probs


def main():
    dataset = [
        [0.5, -0.2, 0.1],
        [0.9, 0.4, -0.3],
        [-0.6, 0.2, 0.8],
    ]
    targets = [0, 1, 1]

    print("=== Tiny Neural Network (NumPy + math) ===")

    total_loss = 0.0
    correct = 0
    for i in range(len(dataset)):
        features = dataset[i]
        probs = forward(features)
        pred = np.argmax(probs)
        loss = cross_entropy(probs, targets[i])
        total_loss = total_loss + loss
        if pred == targets[i]:
            correct = correct + 1
        print(f"sample {i}: probs={probs} pred={pred} target={targets[i]} loss={loss}")

    avg_loss = total_loss / len(dataset)
    accuracy = correct / len(dataset)
    print(f"average loss: {avg_loss}")
    print(f"accuracy: {accuracy}")


if __name__ == "__main__":
    main()