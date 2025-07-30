# Goal Oriented Planning Agent with SFOL  
**Assignment Year: 2024-2025**

This project focuses on building a goal-oriented intelligent agent that navigates a maze by reasoning, planning, and executing actions. It uses Java with a custom Simplified First Order Logic (SFOL) framework for defining and processing knowledge bases.

## Overview

The agent operates in a maze containing walls, keys, doors, and an exit. Its goal is to sense the environment, process percepts, and reason through logic-based rules to achieve its objective. The project progresses from reactive behavior to sophisticated planning using iterative deepening search.

## Features
- **Agent Architecture**: BDI framework with belief, desire, and intention knowledge bases.
- **Reasoning**: Implements forward chaining inference for logical decision-making.
- **Planning**: Uses iterative deepening search to find optimal action sequences.
- **Custom SFOL Framework**: Defines rules and actions using a simplified first-order logic syntax.

## Code Structure
- **Logic Package**: Includes classes for predicates, sentences, and terms in SFOL.
- **Environment Package**: Contains maze and location classes.
- **Agent Package**: Includes the `MyAgent` class (main development focus) and supporting classes for agent control and planning.
- **Data Files**:
  - `prison.txt`: Defines the maze structure.
  - `percepts.txt`, `program.txt`, `actions.txt`: Define percept, program, and action rules for the agent.

## How to Run
1. **Setup**:
   - Install [Eclipse](https://www.eclipse.org/downloads/) and import the project.
   - Place the `src` and `data` folders in the appropriate locations.
2. **Execution**:
   - Run the `RunMe` class to start the program.
   - Use the `HUMAN_DECISION` flag to manually control the agent for testing.
3. **Debugging**:
   - Enable the `DEBUG` flag in the `Agent` class to trace reasoning and decision-making steps.

## Contributors
- **Emmanouil Zagoritis**
- **Kacper Nizielski**

## References
- Eclipse IDE [Setup Guide](https://www.eclipse.org/downloads/).
- Joost Broekens, Symbolic AI Course, Leiden University
