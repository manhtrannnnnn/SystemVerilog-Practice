//----------------------------------------------Detect Sequence----------------------------------------------//
module detect_sequence(
    input clk, rst_n,
    input data_in,
    output valid
);
    localparam  init = 6'b000001,
                S1 = 6'b000010,
                S01 = 6'b000100,
                S101 = 6'b001000,
                S1101 = 6'b010000,
                S01101 = 6'b100000;

    logic [5:0] currentState, nextState;
    
    // State memory
    always_ff @(posedge clk or negedge rst_n) begin : MemoryState
        if(!rst_n) begin
            currentState <= init;
        end
        else begin
            currentState <= nextState;
        end
    end

    // Next State Logic
    always_comb begin : NextState
        case(currentState)
            init: begin
                if(data_in) nextState = S1;
                else nextState = init;
            end
            S1: begin
                if(data_in) nextState = S1;
                else nextState = S01;
            end 
            S01: begin
                if(data_in) nextState = S101;
                else nextState = init;
            end
            S101: begin
                if(data_in) nextState = S1101;
                else nextState = S01;
            end
            S1101: begin
                if(data_in) nextState = S1;
                else nextState = S01101;
            end
            S01101: begin
                nextState = init;
            end
            default: nextState = init;
        endcase
    end

    // Output Logic
    assign valid = (currentState == S01101);
endmodule


module tb_detect_sequence;

    // Inputs
    logic clk;
    logic rst_n;
    logic data_in;

    // Outputs
    logic valid;

    // Instantiate the design under test (DUT)
    detect_sequence dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .valid(valid)
    );

    // Clock generation
    always #5 clk = ~clk; // 10ns clock period

    // Test sequence
    initial begin
        // Initialize inputs
        clk = 0;
        rst_n = 0;
        data_in = 0;

        // Reset the DUT
        #10 rst_n = 1;

        //---------------------Test case 1: Sequence 01101---------------------//
        #10 data_in = 0;  
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  // valid = 1
        #10;

        //---------------------Test case 2: No sequence detected---------------------//
        #10 data_in = 1;  
        #10 data_in = 0; 
        #10 data_in = 0; 
        #10 data_in = 1; 
        #10 data_in = 1; 
        #10 data_in = 1;  
        #10;

        //---------------------Test case 3: Overlapping sequences---------------------//
        #10 data_in = 0;  
        #10 data_in = 1; 
        #10 data_in = 0; 
        #10 data_in = 1;  
        #10 data_in = 1;  
        #10 data_in = 0;  // Valid = 1
        #10 data_in = 0;  
        #10;

        // End of test
        $finish;
    end

    // Monitor signals
    // initial begin
    //     $monitor("Time=%0t clk=%b rst_n=%b data_in=%b valid=%b state=%b",
    //              $time, clk, rst_n, data_in, valid, dut.currentState);
    // end

    // Generate waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end

    // Assertions
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            assert(dut.currentState == 6'b000001)
                else $error("FSM is not in the initial state after reset!");
        end else begin
            // One-hot decode
            assert($onehot(dut.currentState))
                else $error("FSM is not in a valid one-hot encoded state!");

            // Transitions valid
            case (dut.currentState)
                6'b000001: assert((dut.nextState == 6'b000001 && !data_in) || 
                                  (dut.nextState == 6'b000010 && data_in))
                           else $error("Invalid transition from init state!");
                6'b000010: assert((dut.nextState == 6'b000010 && data_in) || 
                                  (dut.nextState == 6'b000100 && !data_in))
                           else $error("Invalid transition from S1 state!");
                6'b000100: assert((dut.nextState == 6'b001000 && data_in) || 
                                  (dut.nextState == 6'b000001 && !data_in))
                           else $error("Invalid transition from S01 state!");
                6'b001000: assert((dut.nextState == 6'b010000 && data_in) || 
                                  (dut.nextState == 6'b000100 && !data_in))
                           else $error("Invalid transition from S101 state!");
                6'b010000: assert((dut.nextState == 6'b000010 && data_in) || 
                                  (dut.nextState == 6'b100000 && !data_in))
                           else $error("Invalid transition from S1101 state!");
                6'b100000: assert(dut.nextState == 6'b000001)
                           else $error("Invalid transition from S01101 state!");
                default: assert(0) else $error("FSM is in an invalid state!");
            endcase

            // 3. Ensure there is no invalid state transition
            assert(dut.currentState == 6'b000001 || dut.currentState == 6'b000010 || dut.currentState == 6'b000100 || dut.currentState == 6'b001000 || dut.currentState == 6'b010000 || dut.currentState == 6'b100000)
                else $error("FSM is stuck or transitioning to an invalid state!");

            // Valid high when sequence detect
            assert(valid == (dut.currentState == 6'b100000))
                else $error("Output valid is high for an incorrect state!");

            // 5. Ensure output is not high for more than one clock cycle
            if (valid)
                assert(!valid || dut.currentState == 6'b100000)
                    else $error("Output valid is high for more than one cycle!");
        end
    end

endmodule

