//-------------------------------------Sudoku-------------------------------------//
class sudoku #(parameter N = 9);
    localparam int COLS = N;
    localparam int ROWS = N;
    localparam int COLS_BLOCK = (N % 2 == 0) ? N / 2: N / 3;
    localparam int ROWS_BLOCK = N / COLS_BLOCK;

    int unsigned puzzel[ROWS][COLS];
    rand int unsigned tmp[ROWS][COLS];
    
    // Constructor
    function new(input int unsigned puzzel[ROWS][COLS]);
      	this.puzzel = puzzel;
    endfunction

    // Constraint for puzzle values
  	constraint value{
      foreach(tmp[ROWS, COLS]){
        	// Random value range
        	tmp[ROWS][COLS] inside {[1:N]};
        
        	// Get the value from puzzel
        	puzzel[ROWS][COLS] != 0 -> tmp[ROWS][COLS] == puzzel[ROWS][COLS];
        }
    }  
     
     // Constraint for the row
    constraint row_cons{
        foreach(tmp[ROWS_OUT, COLS_OUT]){
            foreach(tmp[ROWS_IN, COLS_IN]){
                COLS_OUT != COLS_IN && ROWS_OUT == ROWS_IN -> tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
            }
        }
     }
          
    // Constraint for the col
    constraint col_cons{
        foreach(tmp[ROWS_OUT, COLS_OUT]){
            foreach(tmp[ROWS_IN, COLS_IN]){
                COLS_OUT == COLS_IN && ROWS_OUT != ROWS_IN -> tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
            }
        }
    }

    // Constraint for block
    constraint block_cons {
        foreach (tmp[ROWS_OUT, COLS_OUT]) {
            foreach (tmp[ROWS_IN, COLS_IN]) {
                if ((ROWS_OUT / ROWS_BLOCK == ROWS_IN / ROWS_BLOCK) && (COLS_OUT / COLS_BLOCK == COLS_IN / COLS_BLOCK)) {
                    if (!(ROWS_OUT == ROWS_IN && COLS_OUT == COLS_IN)) {
                        tmp[ROWS_OUT][COLS_OUT] != tmp[ROWS_IN][COLS_IN];
                    }
                }
            }
        }
    }


    // Display the result
    function void display();
        foreach (tmp[ROWS]) begin
            foreach (tmp[ROWS][COLS]) begin
                $write("%0d ", tmp[ROWS][COLS]);
            end
            $write("\n");
        end
    endfunction

endclass

module sudoku_tb;
    parameter N = 6;
  	sudoku #(N) sd;
  	int unsigned arr[N][N] = '{
        '{0, 4, 0, 0, 0, 0},
        '{0, 5, 6, 0, 0, 0},
        '{5, 0, 0, 3, 2, 0},
        '{0, 2, 3, 0, 0, 5},
        '{0, 0, 0, 5, 1, 0},
        '{0, 0, 0, 0, 6, 0}
    };

    initial begin
        sd = new(arr);
        assert(sd.randomize());
        sd.display();
    end
endmodule
